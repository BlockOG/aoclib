# aoclib

A library for running [Advent of Code](https://adventofcode.com) solutions using [aocli](https://github.com/sncxyz/aocli),
and for parsing Advent of Code inputs.

 # Examples
```rust
use aoc::Parse;

let line_1 = "first: 85, then: +192, finally: -64";
let line_2 = "first: -157, then: 4, finally: 1000";

fn parse_line(line: &str) -> [i32; 3] {
    let mut parser = line.as_parser();
    [
        parser.between("first: ", ", "),
        parser.between("then: ", ", "),
        parser.after("finally: "),
    ]
    .map(Parse::parse_uw)
}

assert_eq!(line_1.ints::<3, i32>(), [85, 192, -64]);
assert_eq!(parse_line(line_1), [85, 192, -64]);

assert_eq!(line_2.ints::<3, i32>(), [-157, 4, 1000]);
assert_eq!(parse_line(line_2), [-157, 4, 1000]);
```