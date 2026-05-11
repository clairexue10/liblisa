use liblisa::semantics::default::computation::{
    Arg, ArgEncoding, OutputEncoding, SynthesizedComputation,
};
use liblisa::semantics::default::ops::Op;
use liblisa::semantics::IoType;
use liblisa::semantics::default::computation::AsComputationRef;
use liblisa::encoding::bitpattern::MappingOrBitOrder;
 
// SMT expression tree ───────────────────────────────────────────────────────
 
#[derive(Debug, Clone)]
enum SmtExpr {
    Var(String),
    BvConst { value: i128, bits: u32 },
    BvAdd(Box<SmtExpr>, Box<SmtExpr>),
    BvSub(Box<SmtExpr>, Box<SmtExpr>),
    BvMul(Box<SmtExpr>, Box<SmtExpr>),
    BvAnd(Box<SmtExpr>, Box<SmtExpr>),
    BvOr(Box<SmtExpr>, Box<SmtExpr>),
    BvXor(Box<SmtExpr>, Box<SmtExpr>),
    BvNot(Box<SmtExpr>),
    BvShl(Box<SmtExpr>, Box<SmtExpr>),
    BvShr(Box<SmtExpr>, Box<SmtExpr>),
    BvUDiv(Box<SmtExpr>, Box<SmtExpr>),
    BvSDiv(Box<SmtExpr>, Box<SmtExpr>),
    BvURem(Box<SmtExpr>, Box<SmtExpr>),
    BvSRem(Box<SmtExpr>, Box<SmtExpr>),
    BvCmpLt(Box<SmtExpr>, Box<SmtExpr>),
    IsZero(Box<SmtExpr>),
    Ite(Box<SmtExpr>, Box<SmtExpr>, Box<SmtExpr>), //this is for IsZero
    Extract { hi: u32, lo: u32, inner: Box<SmtExpr> },
    SignExt { total_bits: u32, inner: Box<SmtExpr> },
    ZeroExt { total_bits: u32, inner: Box<SmtExpr> },
    Uninterpreted { name: String, args: Vec<SmtExpr>  },
}
 
impl SmtExpr {
    /// Best-effort bit width inference
    fn bit_width(&self) -> u32 {
        match self {
            SmtExpr::Var(_) => 64,
            SmtExpr::BvConst { bits, .. } => *bits,
            SmtExpr::BvAdd(a, _) => a.bit_width(),
            SmtExpr::BvSub(a, _) => a.bit_width(),
            SmtExpr::BvMul(a, _) => a.bit_width(),
            SmtExpr::BvAnd(a, _) => a.bit_width(),
            SmtExpr::BvOr(a, _) => a.bit_width(),
            SmtExpr::BvXor(a, _) => a.bit_width(),
            SmtExpr::BvNot(a) => a.bit_width(),
            SmtExpr::BvShl(a, _) => a.bit_width(),
            SmtExpr::BvShr(a, _) => a.bit_width(),
            SmtExpr::BvUDiv(a, _) => a.bit_width(),
            SmtExpr::BvSDiv(a, _) => a.bit_width(),
            SmtExpr::BvURem(a, _) => a.bit_width(),
            SmtExpr::BvSRem(a, _) => a.bit_width(),
            SmtExpr::BvCmpLt(_, _) => 1,
            SmtExpr::IsZero(_) => 1,
            SmtExpr::Ite(_, b, _) => b.bit_width(),
            SmtExpr::Extract { hi, lo, .. } => hi - lo + 1,
            SmtExpr::SignExt { total_bits, .. } => *total_bits,
            SmtExpr::ZeroExt { total_bits, .. } => *total_bits,
            SmtExpr::Uninterpreted { .. } => 64,
        }
    }
 
    fn to_isle(&self) -> String {
        match self {
            SmtExpr::Var(name) => name.clone(),
 
            SmtExpr::BvConst { value, bits } => {
                let hex_digits = (bits / 4) as usize;
                // Mask to the correct number of bits
                let masked = if *bits < 128 {
                    value & ((1i128 << bits) - 1)  //unclear
                } else {
                    *value
                };
                format!("#x{:0>width$x}", masked, width = hex_digits)
            }
 
            SmtExpr::BvAdd(a, b) => format!("(bvadd {} {})", a.to_isle(), b.to_isle()),
            SmtExpr::BvSub(a, b) => format!("(bvsub {} {})", a.to_isle(), b.to_isle()),
            SmtExpr::BvMul(a, b) => format!("(bvmul {} {})", a.to_isle(), b.to_isle()),
            SmtExpr::BvAnd(a, b) => format!("(bvand {} {})", a.to_isle(), b.to_isle()),
            SmtExpr::BvOr(a, b) => format!("(bvor {} {})", a.to_isle(), b.to_isle()),
            SmtExpr::BvXor(a, b) => format!("(bvxor {} {})", a.to_isle(), b.to_isle()),
            SmtExpr::BvNot(a) => format!("(bvnot {})", a.to_isle()),
            SmtExpr::BvShl(a, b) => format!("(bvshl {} {})", a.to_isle(), b.to_isle()),
            SmtExpr::BvShr(a, b) => format!("(bvashr {} {})", a.to_isle(), b.to_isle()),
            SmtExpr::BvUDiv(a, b) => format!("(bvudiv {} {})", a.to_isle(), b.to_isle()),
            SmtExpr::BvSDiv(a, b) => format!("(bvsdiv {} {})", a.to_isle(), b.to_isle()),
            SmtExpr::BvURem(a, b) => format!("(bvurem {} {})", a.to_isle(), b.to_isle()),
            SmtExpr::BvSRem(a, b) => format!("(bvsrem {} {})", a.to_isle(), b.to_isle()),
 
            SmtExpr::BvCmpLt(a, b) => {
                format!("(ite (bvslt {} {}) #x0000000000000001 #x0000000000000000)",
                    a.to_isle(), b.to_isle())
            }
 
            SmtExpr::IsZero(a) => {
                let zero = SmtExpr::BvConst { value: 0, bits: a.bit_width() };
                format!("(= {} {})", a.to_isle(), zero.to_isle())
            }
 
            SmtExpr::Ite(cond, then_, else_) => {
                format!("(ite {} {} {})",
                    cond.to_isle(), then_.to_isle(), else_.to_isle())
            }
 
            SmtExpr::Extract { hi, lo, inner } => {
                format!("(extract {} {} {})", hi, lo, inner.to_isle())
            }
 
            SmtExpr::SignExt { total_bits, inner } => {
                let extend_by = total_bits - inner.bit_width();
                format!("(sign_ext {} {})", extend_by, inner.to_isle())
            }
 
            SmtExpr::ZeroExt { total_bits, inner } => {
                let extend_by = total_bits - inner.bit_width();
                format!("(zero_ext {} {})", extend_by, inner.to_isle())
            }
 
            SmtExpr::Uninterpreted { name, args } => {
                let arg_strs: Vec<_> = args.iter().map(|a| a.to_isle()).collect();
                format!("({} {})", name, arg_strs.join(" "))
            }
        }
    }
}
 
// Arg to SmtExpr ─────────────────────────────────────────────────────────────
 
/// Convert a liblisa Arg into a named SMT variable with the correct extension.
/// `arg_names` maps architectural input index to variable name (e.g. ["r0", "r1"]).
/*
fn arg_to_smt(arg: &Arg, consts: &[i128], arg_names: &[&str]) -> SmtExpr {
    match arg {
        Arg::Input { index, num_bits, encoding } => {
            let name = arg_names
                .get(*index as usize)
                .copied()
                .unwrap_or("unknown");
            let raw = SmtExpr::Var(name.to_string());
            extend(raw, *num_bits as u32, *encoding)
        }
 
        Arg::TinyConst(val) => SmtExpr::BvConst {
            value: *val as i128,
            bits: 64,
        },
 
        Arg::Const(idx) => SmtExpr::BvConst {
            value: consts[*idx as usize],
            bits: 64,
        },
    }
}
*/
 
fn extend(raw: SmtExpr, num_bits: u32, encoding: ArgEncoding) -> SmtExpr {
    // For x86 register operands, LE == BE — no byte swap needed
    let is_signed = matches!(
        encoding,
        ArgEncoding::SignedLittleEndian | ArgEncoding::SignedBigEndian
    );

    // Crop to declared width first
    let cropped = if num_bits < 64 {
        SmtExpr::Extract {
            hi: num_bits - 1,
            lo: 0,
            inner: Box::new(raw),
        }
    } else {
        raw
    };

    // Extend to 64 bits
    if num_bits >= 64 {
        cropped
    } else if is_signed {
        SmtExpr::SignExt {
            total_bits: 64,
            inner: Box::new(cropped),
        }
    } else {
        SmtExpr::ZeroExt {
            total_bits: 64,
            inner: Box::new(cropped),
        }
    }
}
 
// Stack evaluator ───────────────────────────────────────────────────────────
 
fn eval_stack(computation: &SynthesizedComputation, arg_names: &[&str]) -> SmtExpr {
    let mut stack: Vec<SmtExpr> = Vec::new();
    let consts = &computation.consts();
 
    for op in computation.expr().ops() {
        match op {
            Op::Hole(n) => {
                let arg = &computation.arg_interpretation()[*n as usize];
                stack.push(arg_to_smt(arg, consts, arg_names));
            }
 
            Op::Const(val) => {
                stack.push(SmtExpr::BvConst {
                    value: *val as i128,
                    bits: 64,
                });
            }
 
            // Unary
            Op::Not => {
                let a = stack.pop().expect("stack underflow: Not");
                stack.push(SmtExpr::BvNot(Box::new(a)));
            }
 
            Op::IsZero => {
                let a = stack.pop().expect("stack underflow: IsZero");
                stack.push(SmtExpr::IsZero(Box::new(a)));
            }
 
            Op::Crop { num_bits } => {
                let a = stack.pop().expect("stack underflow: Crop");
                stack.push(SmtExpr::Extract {
                    hi: *num_bits as u32 - 1,
                    lo: 0,
                    inner: Box::new(a),
                });
            }
 
            Op::SignExtend { num_bits } => {
                let a = stack.pop().expect("stack underflow: SignExtend");
                // First crop to num_bits, then sign-extend to 64
                let cropped = SmtExpr::Extract {
                    hi: *num_bits as u32 - 1,
                    lo: 0,
                    inner: Box::new(a),
                };
                stack.push(SmtExpr::SignExt {
                    total_bits: 64,
                    inner: Box::new(cropped),
                });
            }
 
            Op::Select { num_skip, num_take } => {
                let a = stack.pop().expect("stack underflow: Select");
                let lo = *num_skip as u32;
                let hi = lo + *num_take as u32 - 1;
                stack.push(SmtExpr::Extract {
                    hi,
                    lo,
                    inner: Box::new(a),
                });
            }
 
            // Binary 
            Op::Add => {
                let b = stack.pop().expect("stack underflow: Add");
                let a = stack.pop().expect("stack underflow: Add");
                stack.push(SmtExpr::BvAdd(Box::new(a), Box::new(b)));
            }
 
            Op::Sub => {
                let b = stack.pop().expect("stack underflow: Sub");
                let a = stack.pop().expect("stack underflow: Sub");
                stack.push(SmtExpr::BvSub(Box::new(a), Box::new(b)));
            }
 
            Op::Mul => {
                let b = stack.pop().expect("stack underflow: Mul");
                let a = stack.pop().expect("stack underflow: Mul");
                stack.push(SmtExpr::BvMul(Box::new(a), Box::new(b)));
            }
 
            Op::And => {
                let b = stack.pop().expect("stack underflow: And");
                let a = stack.pop().expect("stack underflow: And");
                stack.push(SmtExpr::BvAnd(Box::new(a), Box::new(b)));
            }
 
            Op::Or => {
                let b = stack.pop().expect("stack underflow: Or");
                let a = stack.pop().expect("stack underflow: Or");
                stack.push(SmtExpr::BvOr(Box::new(a), Box::new(b)));
            }
 
            Op::Xor => {
                let b = stack.pop().expect("stack underflow: Xor");
                let a = stack.pop().expect("stack underflow: Xor");
                stack.push(SmtExpr::BvXor(Box::new(a), Box::new(b)));
            }
 
            Op::Shl => {
                let b = stack.pop().expect("stack underflow: Shl");
                let a = stack.pop().expect("stack underflow: Shl");
                stack.push(SmtExpr::BvShl(Box::new(a), Box::new(b)));
            }
 
            Op::Shr => {
                let b = stack.pop().expect("stack underflow: Shr");
                let a = stack.pop().expect("stack underflow: Shr");
                stack.push(SmtExpr::BvShr(Box::new(a), Box::new(b)));
            }
 
            Op::Div => {
                let b = stack.pop().expect("stack underflow: Div");
                let a = stack.pop().expect("stack underflow: Div");
                stack.push(SmtExpr::BvSDiv(Box::new(a), Box::new(b)));
            }
 
            Op::UnsignedDiv => {
                let b = stack.pop().expect("stack underflow: UnsignedDiv");
                let a = stack.pop().expect("stack underflow: UnsignedDiv");
                stack.push(SmtExpr::BvUDiv(Box::new(a), Box::new(b)));
            }
 
            Op::Rem => {
                let b = stack.pop().expect("stack underflow: Rem");
                let a = stack.pop().expect("stack underflow: Rem");
                stack.push(SmtExpr::BvSRem(Box::new(a), Box::new(b)));
            }
 
            Op::UnsignedRem => {
                let b = stack.pop().expect("stack underflow: UnsignedRem");
                let a = stack.pop().expect("stack underflow: UnsignedRem");
                stack.push(SmtExpr::BvURem(Box::new(a), Box::new(b)));
            }
 
            Op::CmpLt => {
                let b = stack.pop().expect("stack underflow: CmpLt");
                let a = stack.pop().expect("stack underflow: CmpLt");
                stack.push(SmtExpr::BvCmpLt(Box::new(a), Box::new(b)));
            }
 
            // Ternary 
            Op::IfZero => {
                let else_ = stack.pop().expect("stack underflow: IfZero else");
                let then_ = stack.pop().expect("stack underflow: IfZero then");
                let cond  = stack.pop().expect("stack underflow: IfZero cond");
                let zero  = SmtExpr::BvConst { value: 0, bits: cond.bit_width() };
                stack.push(SmtExpr::Ite(
                    Box::new(SmtExpr::BvXor( // cond == 0
                        Box::new(SmtExpr::IsZero(Box::new(cond))),
                        Box::new(SmtExpr::BvConst { value: 0, bits: 1 }),
                    )),
                    Box::new(then_),
                    Box::new(else_),
                ));
            }
 
            // Uninterpreted (no direct SMT/ISLE equivalent) 
            Op::Parity => {
                let a = stack.pop().expect("stack underflow: Parity");
                stack.push(SmtExpr::Uninterpreted {
                    name: "parity".to_string(),
                    args: vec![a],
                });
            }
 
            Op::ByteMask => {
                let a = stack.pop().expect("stack underflow: ByteMask");
                stack.push(SmtExpr::Uninterpreted {
                    name: "byte_mask".to_string(),
                    args: vec![a],
                });
            }
 
            Op::BitMask => {
                let a = stack.pop().expect("stack underflow: BitMask");
                stack.push(SmtExpr::Uninterpreted {
                    name: "bit_mask".to_string(),
                    args: vec![a],
                });
            }
 
            Op::TrailingZeros => {
                let a = stack.pop().expect("stack underflow: TrailingZeros");
                stack.push(SmtExpr::Uninterpreted {
                    name: "trailing_zeros".to_string(),
                    args: vec![a],
                });
            }
 
            Op::LeadingZeros => {
                let a = stack.pop().expect("stack underflow: LeadingZeros");
                stack.push(SmtExpr::Uninterpreted {
                    name: "leading_zeros".to_string(),
                    args: vec![a],
                });
            }
 
            Op::PopCount => {
                let a = stack.pop().expect("stack underflow: PopCount");
                stack.push(SmtExpr::Uninterpreted {
                    name: "popcount".to_string(),
                    args: vec![a],
                });
            }
 
            Op::SwapBytes { num_bits } => {
                let a = stack.pop().expect("stack underflow: SwapBytes");
                stack.push(SmtExpr::Uninterpreted {
                    name: format!("bswap{}", num_bits),
                    args: vec![a],
                });
            }
 
            Op::Rol { num_bits } => {
                let b = stack.pop().expect("stack underflow: Rol amount");
                let a = stack.pop().expect("stack underflow: Rol value");
                stack.push(SmtExpr::Uninterpreted {
                    name: format!("rol{}", num_bits),
                    args: vec![a, b],
                });
            }
 
            Op::CarrylessMul => {
                let b = stack.pop().expect("stack underflow: CarrylessMul");
                let a = stack.pop().expect("stack underflow: CarrylessMul");
                stack.push(SmtExpr::Uninterpreted {
                    name: "carryless_mul".to_string(),
                    args: vec![a, b],
                });
            }
 
            Op::DepositBits => {
                let b = stack.pop().expect("stack underflow: DepositBits");
                let a = stack.pop().expect("stack underflow: DepositBits");
                stack.push(SmtExpr::Uninterpreted {
                    name: "deposit_bits".to_string(),
                    args: vec![a, b],
                });
            }
 
            Op::ExtractBits => {
                let b = stack.pop().expect("stack underflow: ExtractBits");
                let a = stack.pop().expect("stack underflow: ExtractBits");
                stack.push(SmtExpr::Uninterpreted {
                    name: "extract_bits".to_string(),
                    args: vec![a, b],
                });
            }
        }
    }
 
    assert_eq!(stack.len(), 1, "stack must have exactly one result after evaluation");
    stack.pop().unwrap()
}
 
// Public API ────────────────────────────────────────────────────────────────
 
/// Derive variables to represent registers from a SynthesizedComputation by scanning all
/// Arg::Input entries and generating "r0", "r1", ... for each distinct index.
///
/*
pub fn post_process_registers(computation: &SynthesizedComputation) -> Vec<String> {
    let num_inputs = computation
        .arg_interpretation()
        .iter()
        .filter_map(|arg| match arg {
            Arg::Input { index, .. } => Some(*index as usize + 1),
            _ => None,
        })
        .max()
        .unwrap_or(0);
 
    (0..num_inputs).map(|i| format!("r{}", i)).collect()
}
pub fn derive_arg_names(computation: &SynthesizedComputation)->Vec<String>{

}
*/
/*
pub fn derive_vars_from_encoding(encoding: &Encoding)->Vec<String>{
    let mut names = vec![]
    
    for part in &encoding.parts {
        // line 478 — was Mapping::Imm, should be:
        if let MappingOrBitOrder::Imm { locations, .. } = &part.mapping {

    // line 487 — the compiler suggests several options
    // look at what type output.inputs actually contains
    // based on the dataflow output we saw earlier:
    // [Reg(RAX)[0..7]] <= { Reg(RAX)[0..7] v0 }
    // the inputs are likely Source or FlowInput variants, not Input::Reg{
            for loc in locations {
                names[loc.input_index as usize] = "imm32".to_string();
            }
        }
    }

    for output in &encoding.dataflows.outputs {
        for input in &output.inputs {
            if let Input::Reg(reg, ..) = input {
                names[input.index()] = format!("{:?}", reg).to_lowercase();
            }
        }
    }

    names
}
*/


pub fn generate_isle_spec(
    arg_names: &[&str],
    computation: &SynthesizedComputation,
) -> String {
    let expr = eval_stack(computation, arg_names);
    let isle_expr = expr.to_isle();
    let params = arg_names.join(" ");
 
    match &computation.output_type() {
        IoType::Integer { num_bits: 1 } => {
            // 1-bit output — a CPU flag; endianness is irrelevant for a single bit
            format!("(= rd {})", isle_expr)
        }
 
        IoType::Integer { num_bits } => {
            // Crop to declared output width
            let cropped = format!("(extract {} 0 {})", num_bits - 1, isle_expr);
 
            // Apply bswap if output is little-endian
            let final_expr = match computation.output_encoding() {
                OutputEncoding::UnsignedBigEndian => cropped,
                OutputEncoding::UnsignedLittleEndian => {
                    format!("(bswap{} {})", num_bits, cropped)
                }
            };
 
            format!( "(= rd {})", final_expr )
        }

        IoType::Bytes { num_bytes } => {
            // Byte vector output — no direct ISLE mapping, emit a warning comment
            format!(
                "; WARNING: byte output ({} bytes) — manual spec needed\n((= rd {}))",
                num_bytes, isle_expr
            )
        }
    }
}