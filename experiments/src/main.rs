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
        };

        write!(f, "{}", name)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Protocol {
    Clear,
    Yao,
    Gmw,
}

use Protocol::*;

impl Display for Protocol {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let name = match self {
            Clear => "clear",
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

    fn inputs(&self, root_dir: &Path) -> Vec<PathBuf> {
        let parties = self.parties();

        let mut ret = Vec::with_capacity(parties.len());
        for party in parties {
            let mut path = root_dir.to_owned();
            path.push(format!("input/{}", party));
            fs::create_dir_all(&path).expect("TODO");
            path.push(format!("{}-{}.txt", self.program, self.input_size));
            let mut f = fs::File::create(&path).expect("TODO");

            let input = match self.program {
                Hamming => {
                    if party.eq("A") {
                        "0"
                    } else {
                        "1"
                    }
                }
                _ => todo!(),
            };
            let inputs = (0..self.input_size)
                .map(|_| input)
                .collect::<Vec<&str>>()
                .join("\n");
            f.write_all(inputs.as_bytes()).expect("TODO");
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

    fn run(&self, root_dir: &Path, handlebars: &mut Handlebars) -> Duration {
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
                    .arg("-q")
                    .args(["-d", &data_dir])
                    .args(["-p", party])
                    .args(["-c", &hosts])
                    .arg(&program)
            ); */
            let handle = Command::new("symphony")
                .arg("par")
                .arg("-q")
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
}

fn input_sizes(protocol: Protocol, program: Program) -> Vec<usize> {
    [100, 200, 300, 400, 500].to_vec()
}

fn benchmarks() -> Vec<Benchmark> {
    let languages = [Symphony];
    let programs = [Hamming];
    let protocols = [Clear, Gmw];
    let party_sizes = [2];

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

fn update_path() {
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

    update_path();
    stdlib(root_dir.path());

    let templates = [("hamming", "templates/hamming.sym.template")];

    for (name, path) in templates {
        handlebars.register_template_file(name, path).expect("TODO");
    }

    for b in benchmarks() {
        println!(
            "{},{}",
            b,
            b.run(root_dir.path(), &mut handlebars).as_millis()
        );
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
