//! `check_perfdata` allows you to build a monitoring plugin by merely writing out one or more
//! performance data lines and running them through `check_perfdata`. That way, you can forego a
//! lot of boilerplate in your custom monitoring checks, and more often than not a simple bash
//! script that `exec`s `check_perfdata` at the end will suffice.

use std::io;
use std::fmt;
use std::str::FromStr;  // Needed for perfdata::Datum::from_str()
use structopt::StructOpt;
use perfdata;
use perfdata::ExitCode;
use perfdata::ServiceStatus;
use perfdata::HostStatus;

#[derive(Debug)]
enum SubjectType {
    Host,
    Service,
}

#[derive(Debug)]
enum PrimaryPerfDatumChoice {
    Unok,
    First,
    None,
    Specific(String),
}

#[derive(Debug)]
struct InvalidPrimaryPerfDatumChoice {
    err_str: String,
}

impl fmt::Display for InvalidPrimaryPerfDatumChoice {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.err_str)
    }
}

impl FromStr for PrimaryPerfDatumChoice {
    type Err = InvalidPrimaryPerfDatumChoice;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "unok" => Ok(PrimaryPerfDatumChoice::Unok),
            "first" => Ok(PrimaryPerfDatumChoice::First),
            "none" => Ok(PrimaryPerfDatumChoice::None),
            specified => Ok(PrimaryPerfDatumChoice::Specific(specified.to_string())),
        }
    }
}

#[derive(Debug)]
struct InvalidSubjectType {
    err_str: String,
}

impl fmt::Display for InvalidSubjectType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.err_str)
    }
}

impl SubjectType {
    fn variants() -> [&'static str; 2] {
        ["service", "host"]
    }
}

impl FromStr for SubjectType {
    type Err = InvalidSubjectType;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "host" | "Host" => Ok(SubjectType::Host),
            "service" | "Service" => Ok(SubjectType::Service),
            _ => Err(InvalidSubjectType { err_str: format!("Invalid object type: '{}'", s) } ),
        }
    }
}

#[derive(Debug, StructOpt)]
/// Output monitoring plugin status based on perfdata lines read from STDIN.
///
/// The data on STDIN must be either:
///   (a) a perfdatum on each line, or
///   (b) a monitoring plugin's output from which the perfdata can be parsed.
/// The monitoring plugin's input in the case of (b) must conform the Nagios Plugin API:
///   https://www.monitoring-plugins.org/doc/guidelines.html#PLUGOUTPUT
/// And each individual perfdatum in the case of (a) should conform to the perfdata format laid out
/// seperately in that document:
///   https://www.monitoring-plugins.org/doc/guidelines.html#AEN201
struct CmdOpts {
    #[structopt(long, default_value = "service", possible_values = &SubjectType::variants())]
    subject_type: SubjectType,

    #[structopt(long, default_value = "none")]
    /// The primary perfdatum will be printed on the first line, after the status text. By default
    /// (which can be made explicit with the `none` value), all the input perfdata are printed
    /// _after_ the first line (and any other extra non-perfdata output specified via
    /// `--extra-output`). With `unok`, the first of the _least_ okay values (if there is, in fact,
    /// any not-OK value) will be made primary. With `first`, the first perfdatum read from STDIN
    /// will be made primary, regardless of its status, and explicit perfdatum can be selected as
    /// primary by means of its label.
    primary_perfdatum: PrimaryPerfDatumChoice,

    #[structopt(long)]
    /// Normally, the plugin's primary (first line of) output will start with `OK`, `WARNING`,
    /// `CRITICAL`, `UNKNOWN`, `UP` or `DOWN`. Using this flag will omit these status codes. Note
    /// that the plugin will still exit with the appropriate “exit code” between 0 and 3.
    omit_status_code: bool,

    #[structopt(long)]
    /// By default, all the input perfdata will be reoutputted by this plugin. This reoutputting
    /// can be suppressed with this flag. Even with this flag, the primary perfdatum may still be
    /// outputted depending on the `--primary-perfdatum` flag.
    omit_extra_perfdata: bool,
    // BTW: I dislike the use of negatives in the names of booleans as much as the next person, but
    // `structopt` doesn't allow a positive default value for an option flag, which kinda makes
    // sense, come to think of it.

    #[structopt(long)]
    /// Sometimes, you may wish to include extra output to aid troubleshooting for the people
    /// seeing the plugin output, such as the oldest 5 elements in a queue. This content will
    /// always be included _after_ the first line, and _before_ the non-primary perfdata lines.
    extra_output: Vec<String>,
}

fn main() {
    let opt = CmdOpts::from_args();

    let mut buffer = String::new();
    let mut perfdata = perfdata::Data::new();
    let mut parse_errors: Vec<String> = Vec::new();
    while let Ok(bytes_read) = io::stdin().read_line(&mut buffer) {
        if bytes_read == 0 {
            break;
        }
        if &buffer[bytes_read - 1..] == "\n" {
            buffer.truncate(bytes_read - 1);  // Discard newline
        }
        match perfdata::Datum::from_str(&buffer) {
            Ok(perfdatum) => perfdata.add_distinct(perfdatum).unwrap(),
            Err(err) => parse_errors.push(format!("'{}': {}", buffer, err)),
        }
        buffer.clear();
    }

    let status: ServiceStatus = if parse_errors.len() > 0 {
        ServiceStatus::Unknown
    } else {
        ServiceStatus::from(&perfdata)
    };
    let status: Box<dyn ExitCode> = match opt.subject_type {
        SubjectType::Service => Box::new(status),
        SubjectType::Host => Box::new(HostStatus::from(&status)),
    };
    if !opt.omit_status_code {
        print!("{}", status);
    }

    let exit_code = status.exit_code();
    let primary_perfdatum: Option<&perfdata::Datum>;

    if parse_errors.len() > 0 {
        if !opt.omit_status_code {
            print!(" ");
        }
        print!("{}", parse_errors[0]);
    } else if exit_code > 0 {
        if !opt.omit_status_code {
            print!(" ");
        }
        print!("{}", perfdata.first_of_least_ok_values_humanized().unwrap());
    }

    primary_perfdatum = match opt.primary_perfdatum {
        PrimaryPerfDatumChoice::Unok => perfdata.first_least_ok(),
        PrimaryPerfDatumChoice::First => perfdata.into_iter().nth(0),
        PrimaryPerfDatumChoice::Specific(label) => perfdata.get_by_label(&label),
        PrimaryPerfDatumChoice::None => None,
    };
    if let Some(some_primary_perfdatum) = primary_perfdatum {
        print!(" |{}", some_primary_perfdatum);
    }

    print!("\n");  // End of first/primary line

    if parse_errors.len() > 1 {
        print!("{}", parse_errors[1..].join("\n"));
    }

    for v in perfdata.remainder_of_unok_values_humanized() {
        print!("{}\n", v);
    }

    for e_out in opt.extra_output {
        print!("{}\n", e_out);
    }

    if !opt.omit_extra_perfdata {
        let mut extra_perfdata: Vec<&perfdata::Datum> = Vec::new();
        for datum in perfdata.into_iter() {
            match primary_perfdatum {
                Some(d1) if d1.label == datum.label => continue,
                _ => extra_perfdata.push(&datum),
            }
        }
        if extra_perfdata.len() > 0 {
            print!("|");
            for datum in extra_perfdata.into_iter() {
                print!("{}\n", datum);
            }
        }
    }

    std::process::exit(i32::from(exit_code));
}

#[cfg(test)]
mod tests {
    use assert_cmd::Command;  // Add methods on commands
    use predicates::prelude::*;  // Used for writing assertions

    #[test]
    fn test_implicit_service_ok() {
        let mut cmd = Command::cargo_bin("check_perfdata").unwrap();
        let assert = cmd
            .write_stdin("latency=100ms;100;500\n")
            .assert();
        assert
            .code(0)
            .stdout(predicate::eq("OK\n|'latency'=100ms;100;500;;\n"));
    }

    #[test]
    fn test_explicit_service_ok() {
        let mut cmd = Command::cargo_bin("check_perfdata").unwrap();
        let assert = cmd
            .arg("--subject-type").arg("service")
            .write_stdin("latency=100ms;100;500\n")
            .assert();
        assert
            .code(0)
            .stdout(predicate::eq("OK\n|'latency'=100ms;100;500;;\n"));
    }

    #[test]
    fn test_host_ok() {
        let mut cmd = Command::cargo_bin("check_perfdata").unwrap();
        let assert = cmd
            .arg("--subject-type").arg("host")
            .write_stdin("latency=100ms;100;500\n")
            .assert();
        assert
            .code(0)
            .stdout(predicate::eq("UP\n|'latency'=100ms;100;500;;\n"));
    }

    #[test]
    fn test_service_warning() {
        let mut cmd = Command::cargo_bin("check_perfdata").unwrap();
        let assert = cmd
            .write_stdin("latency=101ms;100;500\n")
            .assert();
        assert
            .code(1)
            .stdout(predicate::eq("WARNING latency = 101ms > 100ms [warn-max]\n|'latency'=101ms;100;500;;\n"));

        let mut cmd = Command::cargo_bin("check_perfdata").unwrap();
        let assert = cmd
            .write_stdin("cash=-10;0:;-100:\n")
            .assert();
        assert
            .code(1)
            .stdout(predicate::eq("WARNING cash = -10 < 0 [warn-min]\n|'cash'=-10;;-100:;;\n"));
    }

    #[test]
    fn test_service_critical() {
        let mut cmd = Command::cargo_bin("check_perfdata").unwrap();
        let assert = cmd
            .write_stdin("latency=501ms;100;500\n")
            .assert();
        assert
            .code(2)
            .stdout(predicate::eq("CRITICAL latency = 501ms > 500ms [crit-max]\n|'latency'=501ms;100;500;;\n"));

        let mut cmd = Command::cargo_bin("check_perfdata").unwrap();
        let assert = cmd
            .write_stdin("cash=-101;0:;-100:\n")
            .assert();
        assert
            .code(2)
            .stdout(predicate::eq("CRITICAL cash = -101 < -100 [crit-min]\n|'cash'=-101;;-100:;;\n"));
    }

    #[test]
    fn test_invalid_range() {
        let mut cmd = Command::cargo_bin("check_perfdata").unwrap();
        let assert = cmd
            .write_stdin("latency=501ms;invalidrange;500\n")
            .assert();
        assert
            .code(3)
            .stdout(predicate::eq("UNKNOWN 'latency=501ms;invalidrange;500': invalid range 'invalidrange'\n"));
    }

    #[test]
    fn test_omit_status_code() {
        let mut cmd = Command::cargo_bin("check_perfdata").unwrap();
        let assert = cmd
            .arg("--omit-status-code")
            .write_stdin("latency=10ms;100;500\n")
            .assert();
        assert
            .code(0)
            .stdout(predicate::eq("\n|'latency'=10ms;100;500;;\n"));
    }

    #[test]
    fn test_extra_output() {
        let mut cmd = Command::cargo_bin("check_perfdata").unwrap();
        let assert = cmd
            .arg("--extra-output").arg("A line with shit.")
            .arg("--extra-output").arg("A line with more shit.")
            .write_stdin("latency=10ms;100;500\n")
            .assert();
        assert
            .code(0)
            .stdout(predicate::eq("OK\nA line with shit.\nA line with more shit.\n|'latency'=10ms;100;500;;\n"));
    }

    #[test]
    fn test_least_ok_primary_perfdatum() {
        let mut cmd = Command::cargo_bin("check_perfdata").unwrap();
        let assert = cmd
            .arg("--primary-perfdatum").arg("unok")
            .write_stdin("latency=10ms;100;500\nsize=100KB;50;200\n'free space'=10%;20:;15:\n")
            .assert();
        assert
            .code(2)
            .stdout(predicate::eq("CRITICAL free space = 10% < 15% [crit-min] |'free space'=10%;20:;15:;0;100\nsize = 100KB > 50KB [warn-max]\n|'latency'=10ms;100;500;;\n'size'=100KB;50;200;;\n"));
    }

    #[test]
    fn test_worst_values_printed_first() {
        let mut cmd = Command::cargo_bin("check_perfdata").unwrap();
        let assert = cmd
            .write_stdin("latency=10ms;100;500\nsize=100KB;50;200\n'free space'=10%;20:;15:\n")
            .assert();
        assert
            .code(2)
            .stdout(predicate::eq("CRITICAL free space = 10% < 15% [crit-min]\nsize = 100KB > 50KB [warn-max]\n|'latency'=10ms;100;500;;\n'size'=100KB;50;200;;\n'free space'=10%;20:;15:;0;100\n"));
    }
}
