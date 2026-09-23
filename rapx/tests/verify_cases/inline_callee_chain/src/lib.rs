fn parse(args: &Vec<String>) -> Option<Box<usize>> {
    if args.is_empty() {
        None
    } else {
        Some(Box::new(args.len()))
    }
}

pub fn entry(_a: u8, _b: u8, _c: u8) -> usize {
    let argv: Vec<String> = std::env::args().skip(1).collect();
    match parse(&argv) {
        Some(n) => *n,
        None => {
            eprintln!("{}", argv.len());
            1
        }
    }
}
