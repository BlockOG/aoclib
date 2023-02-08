use std::{env, fs, path::Path, time::Instant};

type Input<'a> = &'a [String];
type Part<T> = fn(Input) -> T;

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

pub fn run<T1, T2>(part_1: Option<Part<T1>>, part_2: Option<Part<T2>>)
where
    T1: ToString,
    T2: ToString,
{
    let args: Vec<_> = env::args().collect();
    if args.len() != 3 {
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
        run_part(&data_path, &out_path, part_1);
    } else {
        let Some(part_2) = part_2 else {
            fs::write(unimplemented_path, "").unwrap();
            return;
        };
        implemented(&unimplemented_path);
        run_part(&data_path, &out_path, part_2);
    }
}

fn run_part<T>(data_path: &Path, out_path: &Path, part_n: Part<T>)
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
    let input: Vec<_> = input.lines().map(|s| s.to_string()).collect();
    let start = Instant::now();
    let answer = part_n(&input);
    let time = start.elapsed().as_nanos();
    let answer = answer.to_string();
    fs::write(out_path.join("answer"), answer).unwrap();
    fs::write(out_path.join("time"), time.to_string()).unwrap();
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
