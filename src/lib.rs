//! A library for running [Advent of Code](https://adventofcode.com) solutions using [aocli](https://github.com/sncxyz/aocli),
//! and for parsing Advent of Code inputs.
//!
//! # Examples
//! ```
//! use aoc::Parse;
//!
//! let line_1 = "first: 85, then: +192, finally: -64";
//! let line_2 = "first: -157, then: 4, finally: 1000";
//!
//! fn parse_line(line: &str) -> [i32; 3] {
//!     let mut parser = line.as_parser();
//!     [
//!         parser.between("first: ", ", "),
//!         parser.between("then: ", ", "),
//!         parser.after("finally: "),
//!     ]
//!     .map(Parse::parse_uw)
//! }
//!
//! assert_eq!(line_1.ints::<3, i32>(), [85, 192, -64]);
//! assert_eq!(parse_line(line_1), [85, 192, -64]);
//!
//! assert_eq!(line_2.ints::<3, i32>(), [-157, 4, 1000]);
//! assert_eq!(parse_line(line_2), [-157, 4, 1000]);
//! ```
mod input;
mod parse;

use std::{env, fs, path::Path, time::Instant};

pub use input::{Input, Lines};
pub use parse::{Ints, IterUnwrap, Parse, Parser, UInts};

type Part<T> = fn(Input) -> T;

/// A macro for running with [aocli](https://github.com/sncxyz/aocli).
///
/// Inserts `fn main` and passes your part 1 and part 2 functions to the `aoclib` library where applicable.
///
/// - `aoc::parts!();` if neither part is implemented
/// - `aoc::parts!(1);` if only part 1 is implemented (`fn part_1`)
/// - `aoc::parts!(2);` if only part 2 is implemented (`fn part_2`)
/// - `aoc::parts!(1, 2);` if both parts are implemented
#[macro_export]
macro_rules! parts {
    () => {
        fn main() {
            aoc::run::<u8, u8>(None, None);
        }
    };
    (1) => {
        fn main() {
            aoc::run::<_, u8>(Some(part_1), None);
        }
    };
    (2) => {
        fn main() {
            aoc::run::<u8, _>(None, Some(part_2));
        }
    };
    (1, 2) => {
        fn main() {
            aoc::run(Some(part_1), Some(part_2));
        }
    };
}

/// The function that `aoc::parts!` inserts into `fn main`.
///
/// Runs one of the parts with one of the puzzle inputs, depending on the command line arguments passed.
///
/// Writes the puzzle answer and timing to files in `/data/[input]/[part]/out` so that `aocli` can read them.
pub fn run<T1, T2>(part_1: Option<Part<T1>>, part_2: Option<Part<T2>>)
where
    T1: ToString,
    T2: ToString,
{
    let args: Vec<_> = env::args().collect();
    if args.len() != 4 {
        panic!("incorrect number of arguments");
    }
    let data = args[1].as_str();
    let mut data_path = Path::new("data").join(data);
    if !data_path.is_dir() {
        panic!("no data directory");
    }
    let part = args[2].as_str();
    if part != "1" && part != "2" {
        panic!("invalid part argument");
    }
    let average = args[3]
        .as_str()
        .parse::<usize>()
        .expect("invalid average argument");
    if average == 0 {
        panic!("invalid average argument");
    }
    let out_path = data_path.join(part).join("out");
    if out_path.try_exists().unwrap() {
        if !out_path.is_dir() {
            panic!("unexpected out file found");
        }
    } else {
        fs::create_dir_all(&out_path).unwrap();
    }
    data_path.push("input");
    let unimplemented_path = out_path.join("unimplemented");
    if part == "1" {
        let Some(part_1) = part_1 else {
            fs::write(unimplemented_path, "").unwrap();
            return;
        };
        implemented(&unimplemented_path);
        run_part(&data_path, &out_path, part_1, average);
    } else {
        let Some(part_2) = part_2 else {
            fs::write(unimplemented_path, "").unwrap();
            return;
        };
        implemented(&unimplemented_path);
        run_part(&data_path, &out_path, part_2, average);
    }
}

fn run_part<T>(data_path: &Path, out_path: &Path, part_n: Part<T>, average: usize)
where
    T: ToString,
{
    if !data_path.is_file() {
        panic!("no input file");
    }
    let input = fs::read_to_string(data_path).unwrap();
    let input = input.trim_end();
    if input.is_empty() {
        panic!("input file is empty");
    }

    let mut answers = Vec::with_capacity(average);
    let mut total_time = 0;

    for _ in 0..average {
        let lines: Vec<_> = input.lines().collect();
        let input = Input::new(input, &lines);
        let start = Instant::now();
        let answer = part_n(input);
        total_time += start.elapsed().as_nanos();
        answers.push(answer);
    }

    let answers: Vec<_> = answers.into_iter().map(|i| i.to_string()).collect();
    for two_answers in answers.windows(2) {
        if two_answers[0] != two_answers[1] {
            panic!("different answers");
        }
    }
    fs::write(out_path.join("answer"), answers[0].clone()).unwrap();
    fs::write(
        out_path.join("time"),
        (total_time / average as u128).to_string(),
    )
    .unwrap();
}

fn implemented(path: &Path) {
    if path.try_exists().unwrap() {
        if path.is_file() {
            fs::remove_file(path).unwrap();
        } else {
            panic!("unexpected unimplemented directory found");
        }
    }
}
