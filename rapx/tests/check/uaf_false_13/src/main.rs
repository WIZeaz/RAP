fn collect(out: &mut Vec<u8>, rows: &[Vec<u8>]) {
    for row in rows {
        for byte in row.clone() {
            out.push(byte);
        }
    }
}

fn main() {
    let mut out = Vec::new();
    collect(&mut out, &[Vec::new()]);
}
