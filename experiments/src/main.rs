use std::collections::HashMap;
use std::fmt::{Display, Formatter};
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Duration, Instant};
use std::{env, fmt};

use handlebars::Handlebars;
use tempfile::TempDir;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Language {
    Symphony,
    Emp,
    Motion,
}

use Language::*;

impl Display for Language {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let name = match self {
            Symphony => "symphony",
            Emp => "EMP",
            Motion => "MOTION",
        };

        write!(f, "{}", name)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Program {
    Hamming,
    Edit,
    Euclidean,
    Analytics,
    Gcd,
    Lwz,
    Waksman,
}

use Program::*;

impl Display for Program {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let name = match self {
            Hamming => "hamming",
            Edit => "edit",
            Euclidean => "euclidean",
            Analytics => "analytics",
            Gcd => "gcd",
            Lwz => "lwz",
            Waksman => "waksman",
        };

        write!(f, "{}", name)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Protocol {
    Rep,
    Yao,
    Gmw,
}

use Protocol::*;

impl Display for Protocol {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let name = match self {
            Rep => "rep",
            Yao => "yao",
            Gmw => "gmw",
        };

        write!(f, "{}", name)
    }
}

struct Benchmark {
    language: Language,
    program: Program,
    protocol: Protocol,
    party_size: usize,
    input_size: usize,
}

impl Display for Benchmark {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(
            f,
            "{},{},{},{},{}",
            self.language, self.program, self.protocol, self.party_size, self.input_size
        )
    }
}

impl Benchmark {
    fn new(
        language: Language,
        program: Program,
        protocol: Protocol,
        party_size: usize,
        input_size: usize,
    ) -> Option<Benchmark> {
        let party_size_large_enough = 2 <= party_size;

        let party_size_small_enough = party_size <= 12;

        let yao_implies_two_parties = protocol != Yao || party_size == 2;

        let emp_implies_yao = language != Emp || protocol == Yao;

        let motion_implies_gmw = language != Motion || protocol == Gmw;

        if !(party_size_large_enough
            && party_size_small_enough
            && yao_implies_two_parties
            && emp_implies_yao
            && motion_implies_gmw)
        {
            return None;
        }

        let ret = Self {
            language,
            program,
            protocol,
            party_size,
            input_size,
        };

        Some(ret)
    }

    fn parties(&self) -> Vec<String> {
        (0..self.party_size)
            .map(|id| unsafe { char::from_u32_unchecked(65 + id as u32) }.to_string())
            .collect()
    }

    fn hosts(&self) -> String {
        self.parties()
            .iter()
            .map(|party| format!("{},127.0.0.1", party))
            .collect::<Vec<String>>()
            .join(":")
    }

    fn hamming_input(&self, party_a: bool) -> String {
        let bit = if party_a { "0" } else { "1" };
        (0..self.input_size)
            .map(|_| bit)
            .collect::<Vec<_>>()
            .join("\n")
    }

    fn edit_input(&self, party_a: bool) -> String {
        if party_a {
            (0..self.input_size)
                .map(|i| i.to_string())
                .collect::<Vec<_>>()
                .join("\n")
        } else {
            (0..self.input_size)
                .map(|i| if i % 2 == 0 { i } else { 0 }.to_string())
                .collect::<Vec<_>>()
                .join("\n")
        }
    }

    fn euclidean_input(&self, party_a: bool) -> String {
        if party_a {
            (1..=self.input_size)
                .map(|i| format!("{} {}", i, i))
                .collect::<Vec<_>>()
                .join("\n")
        } else {
            let xy = self.input_size + 3;
            format!("{} {}", xy, xy)
        }
    }

    fn analytics_input(&self, party_id: usize) -> String {
        (1..=self.input_size)
            .map(|i| format!("{} {}", party_id + i, party_id + self.input_size + i))
            .collect::<Vec<_>>()
            .join("\n")
    }

    fn gcd_input(&self) -> String {
        self.input_size.to_string()
    }

    fn shuffle_input(&self, party_id: usize) -> String {
        let start = party_id * self.input_size;
        (start..(start + self.input_size))
            .map(|i| i.to_string())
            .collect::<Vec<_>>()
            .join("\n")
    }

    fn inputs(&self, root_dir: &Path) -> Vec<PathBuf> {
        let parties = self.parties();

        let mut ret = Vec::with_capacity(parties.len());
        for (i, party) in parties.iter().enumerate() {
            let mut path = root_dir.to_owned();
            path.push(format!("input/{}", party));
            fs::create_dir_all(&path).expect("TODO");
            path.push(format!("{}-{}.txt", self.program, self.input_size));
            let mut f = fs::File::create(&path).expect("TODO");

            let input = match self.program {
                Hamming => self.hamming_input(party.eq("A")),
                Edit => self.edit_input(party.eq("A")),
                Euclidean => self.euclidean_input(party.eq("A")),
                Analytics => self.analytics_input(if party.eq("A") { 0 } else { 1 }),
                Gcd => self.gcd_input(),
                Lwz => self.shuffle_input(i),
                Waksman => self.shuffle_input(i),
            };

            f.write_all(input.as_bytes()).expect("TODO");
            ret.push(path);
        }

        ret
    }

    fn program(&self, root_dir: &Path, handlebars: &mut Handlebars) -> String {
        let mut template_subst = HashMap::new();
        template_subst.insert("protocol", self.protocol.to_string());
        template_subst.insert("input-size", self.input_size.to_string());

        let program = handlebars
            .render(&self.program.to_string(), &template_subst)
            .expect("TODO");

        let mut path = root_dir.to_owned();
        path.push("bin");
        fs::create_dir_all(&path).expect("TODO");
        path.push(format!(
            "{}-{}-{}.sym",
            self.program, self.protocol, self.input_size
        ));

        let mut f = fs::File::create(&path).expect("TODO");
        f.write_all(program.as_bytes()).expect("TODO");
        path.file_name().unwrap().to_str().unwrap().to_string()
    }

    fn run_symphony(&self, root_dir: &Path, handlebars: &mut Handlebars) -> Duration {
        let parties: Vec<String> = self.parties();
        let hosts = self.hosts();
        let _inputs = self.inputs(root_dir);
        let program = self.program(root_dir, handlebars);

        let mut handles = Vec::with_capacity(self.party_size);

        let data_dir = root_dir.to_owned().to_str().unwrap().to_owned();
        let now = Instant::now();
        for party in &parties {
            /*            println!(
                "{:?}",
                Command::new("symphony")
                    .arg("par")
                    .args(["-d", &data_dir])
                    .args(["-p", party])
                    .args(["-c", &hosts])
                    .arg(&program)
            ); */
            let handle = Command::new("symphony")
                .arg("par")
                .args(["-d", &data_dir])
                .args(["-p", party])
                .args(["-c", &hosts])
                .arg(&program)
                .stdout(std::process::Stdio::null())
                .spawn()
                .expect("TODO");
            handles.push(handle)
        }

        for mut handle in handles {
            assert!(handle.wait().expect("TODO").success());
        }
        now.elapsed()
    }

    fn run(&self, root_dir: &Path, handlebars: &mut Handlebars) -> Duration {
        match self.language {
            Symphony => self.run_symphony(root_dir, handlebars),
            _ => todo!(),
        }
    }
}

fn input_sizes(protocol: Protocol, program: Program) -> Vec<usize> {
    match (protocol, program) {
        (Gmw, Hamming) => [100, 200, 300, 400, 500].to_vec(),
        (_, Hamming) => [10000, 20000, 30000, 40000, 50000].to_vec(),
        (Gmw, Edit) => [2, 3, 4, 5, 6].to_vec(),
        (_, Edit) => [50, 80, 110, 140, 170].to_vec(),
        (Gmw, Euclidean) => [2, 3, 4, 5, 6].to_vec(),
        (_, Euclidean) => [100, 200, 300, 400, 500].to_vec(),
        (Gmw, Analytics) => [2, 3, 4, 5, 6].to_vec(),
        (_, Analytics) => [60, 70, 80, 90, 100].to_vec(),
        (Gmw, Gcd) => [10, 20, 30, 40, 50].to_vec(),
        (_, Gcd) => [500, 600, 700, 800, 900].to_vec(),
        (Gmw, Lwz) => [10, 20, 30, 40, 50, 60, 70, 80, 90, 100].to_vec(),
        (_, Lwz) => [10, 20, 30, 40, 50, 60, 70, 80, 90, 100].to_vec(),
        (Gmw, Waksman) => [10, 20, 30, 40, 50, 60, 70, 80, 90, 100].to_vec(),
        (_, Waksman) => [10, 20, 30, 40, 50, 60, 70, 80, 90, 100].to_vec(),
    }
}

fn benchmarks() -> Vec<Benchmark> {
    let languages = [Symphony];
    let programs = [Lwz, Waksman];
    let protocols = [Rep, Gmw];
    let party_sizes = [3];

    let mut benchmarks = Vec::new();

    for language in languages {
        for program in programs {
            for protocol in protocols {
                for party_size in party_sizes {
                    for input_size in input_sizes(protocol, program) {
                        if let Some(b) =
                            Benchmark::new(language, program, protocol, party_size, input_size)
                        {
                            benchmarks.push(b);
                        }
                    }
                }
            }
        }
    }

    benchmarks
}

const SYMPHONY_DIR: &'static str = "/Users/ian/Projects/symphony-lang";

fn update_path_var() {
    let path_var = env::var("PATH").expect("TODO");
    let mut paths = env::split_paths(&path_var).collect::<Vec<_>>();
    paths.push(PathBuf::from(SYMPHONY_DIR));
    let paths_var = env::join_paths(paths).expect("TODO");
    env::set_var("PATH", &paths_var);
}

fn stdlib(root_dir: &Path) {
    let mut path = root_dir.to_owned();
    path.push("lib");
    fs::create_dir_all(&path).expect("TODO");
    path.push("stdlib.sym");
    fs::copy(format!("{}/data/lib/stdlib.sym", SYMPHONY_DIR), &path).expect("TODO");
}

fn main() {
    let mut handlebars = Handlebars::new();
    let root_dir = TempDir::new().expect("TODO");

    update_path_var();
    stdlib(root_dir.path());

    for program in [Hamming, Edit, Euclidean, Analytics, Gcd, Lwz, Waksman] {
        let program_name = program.to_string();
        let template = format!("templates/{}.sym.template", program_name);
        handlebars
            .register_template_file(&program_name, &template)
            .expect("TODO");
    }

    let samples = 5;

    for b in benchmarks() {
        for _ in 0..samples {
            println!(
                "{},{}",
                b,
                b.run(root_dir.path(), &mut handlebars).as_millis()
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use std::io::Write;

    use handlebars::Handlebars;
    use tempfile::NamedTempFile;
    use tempfile::TempDir;

    #[test]
    fn handlebars_example() {
        let mut handlebars = Handlebars::new();

        handlebars
            .register_template_file("hamming", "templates/hamming.sym.template")
            .unwrap();
        let mut data = std::collections::HashMap::new();
        data.insert("protocol", "gmw");
        data.insert("input-size", "1000");

        println!("{}", handlebars.render("hamming", &data).unwrap());
    }

    #[test]
    fn tempfile_example() {
        let mut file = NamedTempFile::new().unwrap();
        file.write_all("hello world!".as_bytes()).unwrap();
        let (_, path) = file.keep().unwrap();
        println!("{:?}", path);
    }

    #[test]
    fn tempfile_tempdir() {
        let tmp_dir = TempDir::new().unwrap();
        let mut tmp_dir_path = tmp_dir.path().to_owned();
        tmp_dir_path.push("data/bin");
        std::fs::create_dir_all(&tmp_dir_path).unwrap();
        tmp_dir_path.push("hamming.sym");
        let mut f = std::fs::File::create(tmp_dir_path).unwrap();
        f.write_all("hello, world!".as_bytes()).unwrap();
        println!("{:?}", tmp_dir.into_path());
    }
}
