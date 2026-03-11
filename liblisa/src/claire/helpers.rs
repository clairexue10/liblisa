use liblisa::encoding::bitpattern::Bit;

pub struct BitPattern{
    in_bp: String,
    out_bp: Vec<Bit>
}

impl BitPattern{
    pub fn parse_str_to_bit(pattern: &str)->Vec<Bit>{
        let mut char_to_index: HashMap<char, usize> = HashMap::new();
        let mut next_index = 0;
        
        pattern.chars().map(|c| match c {
            '0' => Bit::Fixed(0),
            '1' => Bit::Fixed(1),
            '-' => Bit::DontCare,
            c => {
                let idx = *char_to_index.entry(c).or_insert_with(|| {
                    let i = next_index;
                    next_index += 1;
                    i
                });
                Bit::Part(idx)
            }
        }).collect()
    }

    pub fn bp_to_parts<A: Arch>(bits: &Vec<Bit>, mappings: Vec<PartMapping<A>>) -> Vec<Part<A>> {
        // count bits per part index
        let mut sizes: Vec<usize> = vec![];
        
        for bit in bits.iter() {
            if let Bit::Part(n) = bit {
                if *n >= sizes.len() {
                    sizes.resize(*n + 1, 0);
                }
                sizes[*n] += 1;
            }
        }
    
        sizes.iter().enumerate().map(|(i, &size)| Part {
            size,
            value: 0,
            mapping: mappings[i].clone(),
        }).collect()
    }
}