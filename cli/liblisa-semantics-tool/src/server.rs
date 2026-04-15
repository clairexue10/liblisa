use std::fmt::{Debug, Display};
use std::fs::File;
use std::io::{BufReader, BufWriter, ErrorKind};
use std::path::{Path, PathBuf};
use std::str::FromStr;
use std::time::Instant;

use itertools::Itertools;
use liblisa::arch::Arch;
use liblisa::encoding::dataflows::{AddrTermCalculation, AddrTermSize, Dataflows, Dest, Size, Source};
use liblisa::encoding::Encoding;
use liblisa::instr::{FilterMap, Instruction};
use liblisa::semantics::default::codegen::codegen_computation;
use liblisa::semantics::default::codegen::sexpr::{SExpr, SExprCodeGen};
use liblisa::semantics::default::computation::SynthesizedComputation;
use log::info;
use serde::{Deserialize, Serialize};

use liblisa::encoding::bitpattern::Bit;
use liblisa::semantics::Computation;
use liblisa::instr::InstructionFilter;
//use liblisa::claire::helpers::BitPattern; //where all claire's helper functions are

/// Allows you to query semantics via stdin/stdout.
///
/// The semantics server *instantiates* semantics: it fills the correct registers, flags and immediate values from parts in the encoding.
#[derive(Clone, Debug, clap::Parser)]
pub struct Server {
    /// The path of the JSON file that contains the encodings.
    encodings: PathBuf,

    #[clap(long = "debug")]
    /// When enabled, human-readable semantics are printed to stderr.
    ///
    /// The JSON schema is also printed.
    debug: bool,

    #[clap(long = "cache")]
    /// An optional path for a cache.
    /// If the path does not exist, the lookup table is generated normally and then written to this file.
    /// If the path exists, the lookup table is read directly the file.
    /// This significantly speeds up startup time.
    ///
    /// The cache is not portable between different versions of the semantics server.
    /// No verification is performed on the cache.
    /// You must ensure that you use a different file when using a different set of encodings.
    cache: Option<PathBuf>,
}

#[derive(Serialize, schemars::JsonSchema)]
#[serde(bound(serialize = ""))]
#[schemars(bound = "A: schemars::JsonSchema, A::Reg: schemars::JsonSchema")]
struct TermRepr<A: Arch> {
    value: SourceRepr<A>,
    interpret_as: AddrTermSize,
    shift_right: u8,
    multiply_by: u8,
}

#[derive(Serialize, schemars::JsonSchema)]
#[serde(bound(serialize = ""))]
#[schemars(bound = "A: schemars::JsonSchema, A::Reg: schemars::JsonSchema")]
struct AccessRepr<A: Arch> {
    byte_size: u64,
    sum_of: Vec<TermRepr<A>>,
    offset: i64,
}

#[derive(Serialize, schemars::JsonSchema)]
#[serde(bound(serialize = ""))]
#[schemars(bound = "A: schemars::JsonSchema, A::Reg: schemars::JsonSchema")]
struct OutputRepr<A: Arch> {
    write_target: DestRepr<A>,
    inputs: Vec<SourceRepr<A>>,
    computation: SExpr,
}

#[derive(Serialize, schemars::JsonSchema)]
#[serde(bound(serialize = ""))]
#[schemars(bound = "A: schemars::JsonSchema, A::Reg: schemars::JsonSchema")]
struct Repr<A: Arch> {
    memory: Vec<AccessRepr<A>>,
    write_targets: Vec<OutputRepr<A>>,
}

impl<A: Arch> TermRepr<A> {
    fn from_term(term: AddrTermCalculation, input: SourceRepr<A>) -> TermRepr<A> {
        TermRepr {
            value: input,
            interpret_as: term.size,
            shift_right: term.shift.right(),
            multiply_by: term.shift.mult(),
        }
    }
}

impl<A: Arch> Display for TermRepr<A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({} >> {}) * {}", self.value, self.shift_right, self.multiply_by)
    }
}

#[derive(Copy, Clone, Serialize, schemars::JsonSchema)]
#[serde(bound(serialize = ""))]
#[schemars(bound = "A: schemars::JsonSchema, A::Reg: schemars::JsonSchema")]
enum DestRepr<A: Arch> {
    Reg { reg: A::Reg, size: Size },
    Mem { index: usize, size: Size },
}

impl<A: Arch> From<Dest<A>> for DestRepr<A> {
    fn from(value: Dest<A>) -> Self {
        match value {
            Dest::Reg(reg, size) => DestRepr::Reg {
                reg,
                size,
            },
            Dest::Mem(index, size) => DestRepr::Mem {
                index,
                size,
            },
        }
    }
}

impl<A: Arch> From<DestRepr<A>> for Dest<A> {
    fn from(value: DestRepr<A>) -> Self {
        match value {
            DestRepr::Reg {
                reg,
                size,
            } => Dest::Reg(reg, size),
            DestRepr::Mem {
                index,
                size,
            } => Dest::Mem(index, size),
        }
    }
}

impl<A: Arch> Debug for DestRepr<A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&Dest::<A>::from(*self), f)
    }
}

impl<A: Arch> Display for DestRepr<A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&Dest::<A>::from(*self), f)
    }
}

#[derive(Copy, Clone, Serialize, schemars::JsonSchema)]
#[serde(bound(serialize = ""))]
#[schemars(bound = "A: schemars::JsonSchema, A::Reg: schemars::JsonSchema")]
enum SourceRepr<A: Arch> {
    Dest(DestRepr<A>),
    Imm { index: usize },
    Const { value: u64, num_bits: usize },
    Part(usize),    //newly added: whichever register part N encodes
}

impl<A: Arch> From<Source<A>> for SourceRepr<A> {
    fn from(value: Source<A>) -> Self {
        match value {
            Source::Dest(dest) => SourceRepr::Dest(dest.into()),
            Source::Imm(index) => SourceRepr::Imm {
                index,
            },
            Source::Const {
                value,
                num_bits,
            } => SourceRepr::Const {
                value,
                num_bits,
            },
            Source::Part(n) => SourceRepr::Part(n),
        }
    }
}

impl<A: Arch> From<SourceRepr<A>> for Source<A> {
    fn from(value: SourceRepr<A>) -> Self {
        match value {
            SourceRepr::Dest(dest) => Source::Dest(dest.into()),
            SourceRepr::Imm {
                index,
            } => Source::Imm(index),
            SourceRepr::Const {
                value,
                num_bits,
            } => Source::Const {
                value,
                num_bits,
            },
            SourceRepr::Part(n) => Source::Part(n),
        }
    }
}

impl<A: Arch> Debug for SourceRepr<A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&Source::<A>::from(*self), f)
    }
}

impl<A: Arch> Display for SourceRepr<A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&Source::<A>::from(*self), f)
    }
}

#[derive(Serialize, Deserialize)]
#[serde(bound(serialize = "", deserialize = ""))]
struct Data<A: Arch> {
    encodings: Vec<Encoding<A, SynthesizedComputation>>,
    map: FilterMap<usize>,
}

fn build_filter_map<A: Arch>(encodings: &Path) -> Data<A> {
    eprintln!("Reading...");
    dbg!("hiihi");
    let encodings: Vec<Encoding<A, SynthesizedComputation>> =
        serde_json::from_reader(BufReader::new(File::open(encodings).unwrap())).unwrap();

    eprintln!("Building lookup table...");

    let mut map = FilterMap::new();
    for (index, e) in encodings.iter().enumerate() {
        for filter in e.filters() {
            map.add(filter, index);
        }
    }

    Data {
        encodings,
        map,
    }
}


fn bitpattern_to_symbolic_encoding<A: Arch, C: Computation + Clone + Debug>(
    pattern: &str,
    encoding: Option<&Encoding<A, C>>,
) {
    match encoding {
        Some(encoding) => {
            // Keep all parts symbolic
            let symbolic = encoding
                .instantiate_partially(&vec![None; encoding.parts.len()])
                .unwrap();

            println!("{}", symbolic);
        }
        None => println!("No matching encoding found for pattern: {}", pattern),
    }
}


impl Server {
    pub fn run<A: Arch + schemars::JsonSchema>(&self)
    where
        A::Reg: schemars::JsonSchema,
    {
        if self.debug {
            let schema = schemars::schema_for!(Repr<A>);
            eprintln!("Schema: {}", serde_json::to_string_pretty(&schema).unwrap());
        }

        let start = Instant::now();
        let map: Data<A> = if let Some(cache) = &self.cache {
            match File::open(cache) {
                Ok(file) => {
                    eprintln!("Loading cache from {cache:?}");
                    bincode::deserialize_from(BufReader::new(file)).unwrap()
                },
                Err(e) => {
                    match e.kind() {
                        ErrorKind::NotFound => eprintln!("Creating cache {cache:?}"),
                        _ => eprintln!("Error reading {cache:?}: {e}"),
                    }

                    let map = build_filter_map(&self.encodings);

                    bincode::serialize_into(BufWriter::new(File::create(cache).unwrap()), &map).unwrap();
                    map
                },
            }
        } else {
            build_filter_map(&self.encodings)
        };

        eprintln!("That took {}ms", start.elapsed().as_millis());
        eprintln!("Ready!");

        let stdin = std::io::stdin(); //assume the input is direclty bitpattern
        let mut buf = String::new();

        while stdin.read_line(&mut buf).is_ok() {
            //input = hex
            //let instr = Instruction::from_str(&buf).unwrap(); //
            
            //input = bin
            //let trimmed = buf.trim();  //image if this is bitpattern
            //dbg!(trimmed);
            //if trimmed.is_empty() { 
                //break; 
            //}
            
            //let bitpattern = InstructionFilter::parse(&trimmed);
            let bitpattern = InstructionFilter::parse(&buf);
            dbg!(&bitpattern);
            let instr_smallest = bitpattern.smallest_matching_instruction();
            let instr_largest = bitpattern.largest_matching_instruction();

            dbg!(&instr_smallest);
            dbg!(&instr_largest);

            // Try both
            let result1 = bitpattern.next_matching_instruction(&instr_smallest)
                .and_then(|instr| map.map.filters(&instr).map(|&index| &map.encodings[index]));
            dbg!(&result1);

            //let result2 = map.map.filters(&instr_smallest).map(|&index| &map.encodings[index]);
            //dbg!(&result2);
            //let result3 = map.map.filters(&instr_largest).map(|&index| &map.encodings[index]);
            //dbg!(&result3);
            /*
            let instr = InstructionFilter::smallest_matching_instruction(&bitpattern);
            dbg!(&instr);
            let result = map.map.filters(&instr).map(|&index| &map.encodings[index]); //fn filters'def is in encoding/mod.rs
            //dbg!(&result);
            */
            /*
            let possibilities: Vec<Vec<8>> = trimmed
                .as_bytes()
                .map(|&index| if &trimmed[index]!= '0' || &trimmed[index]!='1')
            */
            /*
            let bytes: Vec<u8> = trimmed
                .as_bytes()
                .chunks(8)
                .map(|chunk| {
                    let s = std::str::from_utf8(chunk).unwrap();
                    u8::from_str_radix(s, 2).unwrap()
                })
                .collect();

            let instr = Instruction::new(&bytes);
            dbg!(instr);
            
            //input = bitpattern
            //let bit_pattern = parse_str_to_bit(&buf) //the output should be a bit pattern in Vec<Bit> form

            let result = map.map.filters(&instr).map(|&index| &map.encodings[index]); //fn filters'def is in encoding/mod.rs
            if let Some(e) = result {
                info!("Matched encoding: {e}");
            }
            */
            /*
            if let Some(encoding) = result {
                for (bit_index, bit) in encoding.bits.iter().enumerate() {
                    match bit {
                        Bit::Part(part_index) => {
                            println!("Bit {} belongs to part {}", bit_index, part_index);
                        }
                        Bit::Fixed(v) => println!("Bit {} is fixed to {}", bit_index, v),
                        Bit::DontCare => println!("Bit {} is don't care", bit_index),
                    }
                }
            }
            */
           
            /*
            let result1 = result.map(|encoding: &Encoding<_, _>| {
                let parts = encoding.extract_parts(&instr_smallest); //extract_parts is in encoding/mod.rs
                let dataflow = encoding.instantiate(&parts).unwrap(); //instantiate is in encoding/mod.rs
                dbg!(&encoding.bits);
                dbg!(&encoding.parts);
                dbg!(&encoding);
                dbg!(&dataflow);
                dataflow //this is a collection of dataflows
                //dbg!(&symbolic);
            });

            let result2 = result.map(|encoding: &Encoding<_, _>| {
                let parts = encoding.extract_parts(&instr_largest); //extract_parts is in encoding/mod.rs
                let dataflow = encoding.instantiate(&parts).unwrap(); //instantiate is in encoding/mod.rs
                dbg!(&encoding.bits);
                dbg!(&encoding.parts);
                dbg!(&encoding);
                dbg!(&dataflow);
                dataflow //this is a collection of dataflows
                //dbg!(&symbolic);
            });

            */
            let result2 = result1.map(|encoding: &Encoding<_, _>| {
                let dataflow = encoding.instantiate_symbolic().unwrap();
                dbg!(&encoding.bits);
                dbg!(&encoding.parts);
                dbg!(&encoding);
                dbg!(&dataflow);
                dataflow
            });

            let result2 = result2.and_then(|dataflow: Dataflows<_, _>|{
                if dataflow.output_dataflows().any(|o| o.computation.is_none()) {
                    None
                } else {
                    Some(Repr {
                        memory: dataflow //this is a collection of dataflows
                            .addresses
                            .iter()
                            .map(|access| AccessRepr {
                                byte_size: access.size.end,
                                sum_of: access
                                    .inputs
                                    .iter()
                                    .zip(access.calculation.terms.iter())
                                    .flat_map(|(&input, term)| {
                                        [TermRepr::from_term(term.primary, input.into())].into_iter().chain(
                                            [term.second_use.map(|term| TermRepr::from_term(term, input.into()))]
                                                .into_iter()
                                                .flatten(),
                                        )
                                    })
                                    .collect(),
                                offset: access.calculation.offset,
                            })
                            .collect(),
                        write_targets: dataflow
                            .outputs
                            .iter()
                            .map(|output| {
                                let mut g = SExprCodeGen::new();
                                let computation = output.computation.as_ref().unwrap();
                                let computation = codegen_computation(&mut g, computation);

                                OutputRepr {
                                    write_target: output.target.into(),
                                    inputs: output.inputs.iter().cloned().map_into().collect(),
                                    computation,
                                }
                            })
                            .collect(),
                    })
                }
            });

            println!("{}", serde_json::to_string(&result2).unwrap());
            if self.debug {
                if let Some(r) = result2 {
                    for (index, item) in r.memory.iter().enumerate() {
                        eprintln!("  Addr[{index}] = {} + 0x{:X}", item.sum_of.iter().join(" + "), item.offset);
                    }

                    for item in r.write_targets.iter() {
                        eprintln!(
                            "  {:?} := {} with inputs {:?}",
                            item.write_target, item.computation, item.inputs
                        );
                    }
                }
            }
         

            buf.clear();
        }
    }
}
