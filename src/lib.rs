//! `perfdata` allows the reading and writing of performance data confirming to the Nagios plugin
//! interface that is also supported by Icinga and other Nagios forks/alternatives.
//!
//! In this somewhat informally standardized plugin interface, performance data can be embedded in
//! a monitoring plugin's standard output. (Monitoring plugins are standalone executables that are
//! executed by a compliant monitoring system.)
//!
//! See https://nagios-plugins.org/doc/guidelines.html#AEN200 for the details of the format.
//! Or, for an unbranded version of the same:
//! https://www.monitoring-plugins.org/doc/guidelines.html#AEN201
//!
//! The Icinga 2 also contains an excellent description of the performance data format. Like me,
//! you may find their description (and otherwise at least their documentation formatting) easier
//! to parse than the Nagios docs.
//!
//! A monitoring plugin
//! https://assets.nagios.com/downloads/nagioscore/docs/nagioscore/3/en/pluginapi.html
//! https://icinga.com/docs/icinga-2/latest/doc/05-service-monitoring/#service-monitoring-plugin-api
//! https://www.monitoring-plugins.org/doc/guidelines.html#PLUGOUTPUT


#[macro_use]
extern crate lazy_static;

use std::cmp::Ordering;
use std::fmt;
use std::str::FromStr;
use std::collections::HashSet;
use std::iter::IntoIterator;
use std::num::ParseFloatError;
use regex::Regex;

#[derive(Debug)]
pub enum ParseError {
    MissingLabel,
    MissingValue,
    InvalidValue(String),
    InvalidFloat,
    InvalidUnit(String),
    InvalidRange(String),
    InvalidMin(String),
    InvalidMax(String),
    InvalidDatum(String),
    InvalidPluginOutput,
    IndistinctLabel(String),
}

impl From<ParseFloatError> for ParseError {
    fn from(_: ParseFloatError) -> Self {
        Self::InvalidFloat
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseError::MissingLabel => write!(f, "missing label"),
            ParseError::MissingValue => write!(f, "missing value"),
            ParseError::InvalidValue(s) => write!(f, "value '{}' doesn't match regexp", s),
            ParseError::InvalidFloat => write!(f, "value cannot be parsed as float"),
            ParseError::InvalidUnit(s) => write!(f, "invalid unit '{}'", s),
            ParseError::InvalidRange(s) => write!(f, "invalid range '{}'", s),
            ParseError::InvalidMin(s) => write!(f, "invalid min '{}'", s),
            ParseError::InvalidMax(s) => write!(f, "invalid max '{}'", s),
            ParseError::InvalidDatum(s) => write!(f, "perfdatum '{}' doesn't match regexp", s),
            ParseError::IndistinctLabel(s) => write!(f, "label '{}' is ambigeous", s),
            ParseError::InvalidPluginOutput => write!(f, "invalid plugin output"),
        }
    }
}

/// A perfdata value is always either a (decimal) number or a literal `U` if “the actual value
/// couldn't be determined”.
#[derive(PartialEq)]
#[derive(PartialOrd)]
#[derive(Debug)]
pub struct Value (Option<f32>,);

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0 {
            None => write!(f, "U"),
            Some(val) => write!(f, "{}", val),
        }
    }
}

impl FromStr for Value {
    type Err = ParseError;

    // In the monitoring plugin interface, `"U"` is used to indicate the absence of a value.
    // Thus, in the case that `"U"` is encountered, `Ok(None)` is returned.
    //
    // When the supplied value could not be recognized as a decimal number by this function,
    // `Err(ParseError::InvalidValue)` is returned. `Err(ParseError::InvalidFloat)` is returned
    // (via `ParseError::from()`) when `f32::from_str()` itself throws an error..
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        lazy_static! {
            static ref RE: Regex = Regex::new(r"^-?\d+(?:.\d+)?$").unwrap();
        }
        if RE.is_match(s) {
            Ok(Self(Some(f32::from_str(s)?)))
        }
        else if s == "U" {
            Ok(Self(None))
        }
        else {
            Err(Self::Err::InvalidValue(s.to_string()))
        }
    }
}

impl std::cmp::PartialEq<Value> for f32 {
    fn eq(&self, other: &Value) -> bool {
        match other.0 {
            None => false,
            Some(val)  => *self == val,
        }
    }
}

impl std::cmp::PartialOrd<Value> for f32 {
    fn partial_cmp(&self, other: &Value) -> Option<Ordering> {
        match other.0 {
            None => None,
            Some(val) => self.partial_cmp(&val),
        }
    }
}

impl std::cmp::PartialEq<f32> for Value {
    fn eq(&self, other: &f32) -> bool {
        match self.0 {
            None => false,
            Some(val) => val == *other,
        }
    }
}

impl std::cmp::PartialOrd<f32> for Value {
    fn partial_cmp(&self, other: &f32) -> Option<Ordering> {
        match self.0 {
            None => None,
            Some(val) => val.partial_cmp(other),
        }
    }
}

/// A perfdata unit of measure (UOM) can help the monitoring system visualize performance data
/// values. Icingaweb2, for example, visualizes percentages as tiny pie diagrams.
#[derive(PartialEq)]
#[derive(Debug)]
pub enum Unit {
    Microseconds,
    Milliseconds,
    Seconds,
    Percentage,
    Bytes,
    Kilobytes,
    Megabytes,
    Terrabytes,
    ContinuousCounter,
    None,  // Units are not obligatory.
// TODO: Extend with all the units that are supported by Icinga 2:
//       https://icinga.com/docs/icinga-2/latest/doc/05-service-monitoring/#performance-data-metrics
}

pub fn value_to_unit_without_si_prefix(val_struct: &Value, unit: Unit) -> (Value, Unit) {
    let (multiplier, new_unit) = match unit {
        Unit::Microseconds => (0.000001, Unit::Seconds),
        Unit::Milliseconds => (0.001, Unit::Seconds),
        Unit::Kilobytes => (1000.0, Unit::Bytes),
        Unit::Megabytes => (1000000.0, Unit::Bytes),
        Unit::Terrabytes => (1000000000.0, Unit::Bytes),
        Unit::Seconds
            | Unit::Bytes
            | Unit::Percentage
            | Unit::ContinuousCounter
            | Unit::None => (1.0 , unit),
    };
    match val_struct.0 {
        None => (Value(None), new_unit),
        Some(val) => (Value(Some(val * multiplier)), new_unit),
    }
}

impl fmt::Display for Unit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Unit::Microseconds => "us",
            Unit::Milliseconds => "ms",
            Unit::Seconds => "s",
            Unit::Percentage => "%",
            Unit::Bytes => "B",
            Unit::Kilobytes => "KB",
            Unit::Megabytes => "MB",
            Unit::Terrabytes => "TB",
            Unit::ContinuousCounter => "c",
            Unit::None => "",
        };
        write!(f, "{}", s)
    }
}

impl FromStr for Unit {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "us" => Ok(Unit::Microseconds),
            "ms" => Ok(Unit::Milliseconds),
            "s" => Ok(Unit::Seconds),
            "%" => Ok(Unit::Percentage),
            "B" => Ok(Unit::Bytes),
            "KB" => Ok(Unit::Kilobytes),
            "MB" => Ok(Unit::Megabytes),
            "TB" => Ok(Unit::Terrabytes),
            "c" => Ok(Unit::ContinuousCounter),
            "" => Ok(Unit::None),
            _ => Err(ParseError::InvalidUnit(s.to_string())),
        }
    }
}

/// The `f32` is wrapped in a struct because infinity for `Min` is represented by omission.
#[derive(PartialEq)]
#[derive(PartialOrd)]
#[derive(Debug)]
pub struct Min(f32);

impl FromStr for Min {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "" => Ok(Min(f32::NEG_INFINITY)),
            _ => match f32::from_str(s) {
                Err(_) => Err(ParseError::InvalidMin(s.to_string())),
                Ok(parsed_float) => Ok(Min(parsed_float)),
            }
        }
    }
}

impl fmt::Display for Min {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0 == f32::NEG_INFINITY {
            Ok(())
        } else {
            f32::fmt(&self.0, f)
        }
    }
}

/// The `f32` is wrapped in a struct because infinity for `Max` is represented by omission.
#[derive(PartialEq)]
#[derive(PartialOrd)]
#[derive(Debug)]
pub struct Max(f32);

impl FromStr for Max {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "" => Ok(Max(f32::INFINITY)),
            _ => match f32::from_str(s) {
                Err(_) => Err(ParseError::InvalidMax(s.to_string())),
                Ok(parsed_float) => Ok(Max(parsed_float)),
            }
        }
    }
}

impl fmt::Display for Max {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0 == f32::INFINITY {
            Ok(())
        } else {
            f32::fmt(&self.0, f)
        }
    }
}

/// As per the monitoring-plugins.org documentation, performance data ranges include the endpoints.
///
/// `lower_bound` ≤ `upper_bound`.
///
/// Contrary to `Min` and `Max`, where both negative and positive infinity are represented by
/// omission, for `Range`, negative infinity is represented by `~` and positive infinity by
/// omission. For example, when represented as a full `Range`:
///   - `~:10` is everything between negative infinity,
///   - `~:` is everything between negative
#[derive(PartialEq)]
#[derive(Debug)]
#[derive(Clone)]
#[derive(Copy)]
pub struct Range {
    lower_bound: f32,
    upper_bound: f32,
    stay_inside_of_bounds: bool,
}

/// A range itself doesn't have to know whether it's a range used to define critical (`RangeType::Crit`)
/// thresholds or warning (`RangeType::Warn`) thresholds.
pub enum RangeType {
    Warn,
    Crit,
}

#[derive(Debug, Clone)]
pub struct RangeInvalid(String);

impl Range {
    pub fn new(lower_bound: f32, upper_bound: f32, stay_inside_of_bounds: bool) -> Result<Self, RangeInvalid> {
        if lower_bound > upper_bound {
            return Err(RangeInvalid(
                format!("range lower bound ({}) should not exceed upper bound ({}", lower_bound, upper_bound)
            ));
        }
        Ok(Range { lower_bound, upper_bound, stay_inside_of_bounds,} )
    }

    /// Is the supplied value either…
    ///   ⓐ inside of the range boundaries (in the case `stay_inside_of_bounds = True`), or
    ///   ⓑ outside of the range boundaries (in case `stay_inside_of_bounds = False`).
    fn is_value_ok(&self, val: &Value) -> bool {
        if self.stay_inside_of_bounds {
            if self.lower_bound > *val {
                return false;
            }
            if self.upper_bound < *val {
                return false;
            }
        }
        else {
            if self.lower_bound <= *val && self.upper_bound >= *val {
                return false;
            }
        }
        return true;
    }
}

impl fmt::Display for Range {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.stay_inside_of_bounds {
            write!(f, "@")?;
        }

        if self.lower_bound != 0.0 {
            if self.lower_bound == f32::NEG_INFINITY {
                write!(f, "~")?;
            } else {
                write!(f, "{}", self.lower_bound)?;
            }

            if self.lower_bound != 0.0 {
                write!(f, ":")?;
            }
        }

        if self.upper_bound != f32::INFINITY {
            write!(f, "{}", self.upper_bound)?;
        }
        Ok(())
    }
}

impl FromStr for Range {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        lazy_static! {
            static ref RE: Regex = Regex::new(r"(?x)
                ^
                (?P<stay_outside_of_bounds_indicator>@)?
                (?:(?P<lower_bound>~|-?[0-9]+(?:\.[0-9]+)?):)?
                (?P<upper_bound>-?[0-9]+(?:\.[0-9]+)?)?
                $
            ").unwrap();
        }

        let caps = match RE.captures(s) {
            Some(re_captures) => re_captures,
            None => return Err(ParseError::InvalidRange(s.to_string())),
        };

        let stay_inside_of_bounds = matches!(caps.name("stay_outside_of_bounds_indicator"), None);

        let lower_bound = match caps.name("lower_bound") {
            None => 0.0,  // When the lower boundary is omitted, it stands for 0.0.
            Some(re_match) => match re_match.as_str() {
                "~" => f32::NEG_INFINITY,
                re_match_str => f32::from_str(re_match_str)?,
            },
        };
        let upper_bound = match caps.name("upper_bound") {
            None => f32::INFINITY,  // Then the upper boundary is omitted, it stands for ∞.
            Some(re_match) => match re_match.as_str() {
                "" => f32::INFINITY,  // XXX: Is this code ever even reached/reachable?
                re_match_str => f32::from_str(re_match_str)?,
            },
        };
        match Range::new(lower_bound, upper_bound, stay_inside_of_bounds) {
            Ok(range) => Ok(range),
            Err(RangeInvalid(s)) => Err(ParseError::InvalidRange(s)),
        }
    }
}

/// `Datum` – a singular piece of performance data.
#[derive(PartialEq)]
#[derive(Debug)]
pub struct Datum {
    pub label: String,
    pub value: Value,
    pub unit: Unit,
    pub min: Min,
    pub max: Max,
    pub warn: Option<Range>,
    pub crit: Option<Range>,
}

impl Datum {
    pub fn is_ok(&self) -> bool {
        !self.is_not_ok()
    }

    pub fn is_not_ok(&self) -> bool {
        self.is_warn() || self.is_crit()
    }

    pub fn is_warn(&self) -> bool {
        match &self.warn {
            None => false,
            Some(warn) => !warn.is_value_ok(&self.value),
        }
    }

    pub fn is_crit(&self) -> bool {
        match &self.crit {
            None => false,
            Some(crit) => !crit.is_value_ok(&self.value),
        }
    }

    fn value_in_range(&self, warn_or_crit: &str, range: &Range) -> String {
        if range.stay_inside_of_bounds && self.value > range.upper_bound {
            format!(
                "{label} = {val}{unit} > {max}{unit} [{warn_or_crit}-max]",
                label = self.label, val = self.value, unit = self.unit, max = range.upper_bound,
                warn_or_crit = warn_or_crit
            )
        }
        else if range.stay_inside_of_bounds && self.value < range.lower_bound {
            format!(
                "{label} = {val}{unit} < {min}{unit} [{warn_or_crit}-min]",
                label = self.label, val = self.value, unit = self.unit, min = range.lower_bound,
                warn_or_crit = warn_or_crit
            )
        }
        else if !range.stay_inside_of_bounds && self.value >= range.lower_bound && self.value <= range.upper_bound {
            format!(
                "{low}{unit} [{t}-low] ≤ {label} = {val}{unit} ≤ {high}{unit} [{t}-high]",
                label = self.label, val = self.value, unit = self.unit, low = range.lower_bound,
                high = range.upper_bound, t = warn_or_crit
            )
        }
        else {
            // TODO: Put in context of range?
            format!("{}={}{}", self.label, self.value, self.unit)
        }
    }

    pub fn simple_status(&self) -> String {
        if self.is_crit() {
            self.value_in_range("crit", &self.crit.unwrap())
        }
        else if self.is_warn() {
            self.value_in_range("warn", &self.warn.unwrap())
        }
        else {
            format!("{}={}{}", self.label, self.value, self.unit)
        }
    }
}

impl FromStr for Datum {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        lazy_static! {
            static ref RE: Regex = Regex::new(r"(?x)
                ^
                (?: (?:'(?P<quoted_label>.+)') | (?P<unquoted_label>[^\x20]+) )
                =
                (?P<value>U|(?:-?[0-9]+(?:\.[0-9]+)?))
                (?P<unit>[a-zA-Z%]+)?
                (?:;
                  (?P<warn>[^;\n]+)?
                  (?:;
                    (?P<crit>[^;\n]+)?
                    (?:;
                      (?P<min>[^;\n]+)?
                      (?:;
                        (?P<max>[^;]+)?
                      )?
                    )?
                  )?
                )?
                \n?
                $
            ").unwrap();
        }
        let caps = match RE.captures(s) {
            None => return Err(ParseError::InvalidDatum(s.to_string())),
            Some(caps) => caps,
        };
        let label: String = match caps.name("quoted_label") {
            Some(quoted_label) => quoted_label.as_str().to_string(),
            None => match caps.name("unquoted_label") {
                Some(unquoted_label) => unquoted_label.as_str().to_string(),
                None => return Err(ParseError::MissingLabel),
            },
        };
        let value: Value = match caps.name("value") {
            Some(value_match) => Value::from_str(value_match.as_str())?,
            None => Value(None),
        };
        let unit: Unit = match caps.name("unit") {
            Some(unit_match) => Unit::from_str(unit_match.as_str())?,
            None => Unit::None,
        };
        let min: Min = match caps.name("min") {
            Some(min_match) => Min::from_str(min_match.as_str())?,
            None => match unit {
                Unit::Percentage => Min(0.0),
                _ => Min(f32::NEG_INFINITY),
            },
        };
        let max: Max = match caps.name("max") {
            Some(max_match) => Max::from_str(max_match.as_str())?,
            None => match unit {
                Unit::Percentage => Max(100.0),
                _ => Max(f32::INFINITY),
            },
        };
        let warn: Option<Range> = match caps.name("warn") {
            Some(warn_match) => Some(Range::from_str(warn_match.as_str())?),
            None => None,
        };
        let crit: Option<Range> = match caps.name("crit") {
            Some(crit_match) => Some(Range::from_str(crit_match.as_str())?),
            None => None
        };
        Ok(Datum {
            label: label,
            value: value,
            unit: unit,
            min: min,
            max: max,
            warn: warn,
            crit: crit,
        })
    }
}

/// The perfdatum label will always be quoted by `Datum::fmt()`, because that saves the headache of
/// figuring out whether it _needs_ to be quoted. Also, all the field seperators are always
/// present, simply because of ease of implementation.
impl fmt::Display for Datum {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "'{}'={}{};", &self.label, &self.value, &self.unit)?;
        if let Some(warn) = &self.warn {
            write!(f, "{}", warn)?;
        }
        write!(f, ";")?;
        if let Some(crit) = &self.crit {
            write!(f, "{}", crit)?;
        }
        write!(f, ";{};{}", &self.min, &self.max)?;
        Ok(())
    }
}

// I would have preferred to use an ordered dictionary.
pub struct Data<'a> {
    datums: Vec<Datum>,

    used_labels: HashSet<String>,

    // FIXME: Please somebody explain to me how I can get of the following error without this hack:
    //        "parameter `'a` is never used: unused parameter"
    _lifetime_hack: &'a bool,
}

#[derive(Debug)]
pub struct IndistinctLabel(String);

const UNIQUE_LABEL_LENGTH: usize = 19;

impl From<IndistinctLabel> for ParseError {
    fn from(err: IndistinctLabel) -> Self {
        Self::IndistinctLabel(err.0)
    }
}

impl<'a> Data<'a> {
    /// Instantiate a `Data` object.
    pub fn new() -> Self {
        Data { datums: Vec::new(), used_labels: HashSet::new(), _lifetime_hack: &true }
    }

    pub fn add_distinct(&mut self, datum: Datum) -> Result<(), IndistinctLabel> {
        let truncated_label = if &datum.label.len() > &UNIQUE_LABEL_LENGTH {
            &datum.label[..UNIQUE_LABEL_LENGTH]
        } else {
            &datum.label
        };
        if self.used_labels.contains(truncated_label) {
            return Err(IndistinctLabel(format!("The first 18 characters of '{}' are already present in the list of perfdata.", datum.label)));
        }

        self.used_labels.insert(String::from(truncated_label));

        self.datums.push(datum);

        Ok(())
    }

    pub fn get_by_label(&self, label: &str) -> Option<&Datum> {
        self.into_iter().find(|&d| { d.label == label })
    }

    pub fn all_ok(&self) -> bool {
        self.into_iter().all(|datum| { datum.is_ok() })
    }

    pub fn any_warn(&self) -> bool {
        self.into_iter().any(|datum| { datum.is_warn() })
    }

    pub fn any_crit(&self) -> bool {
        self.into_iter().any(|datum| { datum.is_crit() })
    }

    pub fn is_unknown(&self) -> bool {
        // If we have no perfdata, we have nothing to base our status on, so we will default to
        // status UNKNOWN.
        self.datums.len() == 0
    }

    /// Return the first perfdatum in the least OK category. That means that, if there are 2
    /// perfdata in a WARNING state, the first of these two will be returned. If besides these two,
    /// there's also a perfdatum in the CRITICAL state, however, then that CRITICAL perfdatum will
    /// be returned.
    pub fn first_least_ok(&self) -> Option<&Datum> {
        self.datums.iter().find(|&d| d.is_crit()).or_else(|| self.datums.iter().find(|&d| d.is_warn()))
    }

    pub fn first_of_least_ok_values_humanized(&self) -> Option<String> {
        if let Some(crit1) = self.datums.iter().find(|&d| d.is_crit()) {
            Some(crit1.simple_status())
        }
        else if let Some(warn1) = self.datums.iter().find(|&d| d.is_warn()) {
            Some(warn1.simple_status())
        }
        else {
            None
        }
    }

    pub fn remainder_of_unok_values_humanized(&self) -> Vec<String> {
        let mut humanized_values: Vec<String> = Vec::new();

        if let Some(first_unok) = self.first_least_ok() {
            for datum in self.datums.iter() {
                if datum.label == first_unok.label {
                    continue;
                }
                if datum.is_not_ok() {
                    humanized_values.push(datum.simple_status());
                }
            }
        }

        humanized_values
    }
}

impl<'a> FromStr for Data<'a> {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        lazy_static! {
            static ref RE: Regex = Regex::new(r"(?xms)
                \A
                (?P<primary_output>[^|\n]+)
                (?:\x20? \| \x20* (?P<primary_perfdatum>[^\n]+))?
                (?:
                  \n
                  (?P<extra_output>[^|]+)?
                  (?:\x20* \| \x20* (?P<extra_perfdatums>.+)?)?
                )?
                \z
            ").unwrap();
        }

        let mut data = Data::new();

        match RE.captures(s) {
            Some(captures) if captures.name("primary_perfdatum").is_some() || captures.name("extra_perfdatums").is_some() => {
                println!("Some: {}", captures.name("primary_output").unwrap().as_str());
                if let Some(datum1_match) = captures.name("primary_perfdatum") {
                    data.add_distinct(Datum::from_str(datum1_match.as_str())?)?;
                };
                if let Some(data_match) = captures.name("extra_perfdatums") {
                    for l in data_match.as_str().lines() {
                        data.add_distinct(Datum::from_str(l)?)?;
                    }
                }
            },
            _ => {
                // No plugin output; assume that these are just newline-separated perfdata lines,
                // which are not part of a monitoring plugin's overall output.
                for l in s.lines() {
                    data.add_distinct(Datum::from_str(l)?)?;
                }
            },
        }

        Ok(data)
    }
}

impl<'a> fmt::Display for Data<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "|")?;
        for datum in self.into_iter() {
            write!(f, "{}\n", datum)?;
        }
        Ok(())
    }
}

impl<'a> IntoIterator for &'a Data<'a> {
    type Item = &'a Datum;

    // XXX: I'd really prefer not to use a box here, but I think I cannot specify the
    //      iterator type for `Vec<>` is private in the `std::` module space.
    type IntoIter = Box<dyn Iterator<Item=&'a Datum> + 'a>;

    fn into_iter(self) -> Box<dyn Iterator<Item=&'a Datum> + 'a> {
        Box::new(self.datums.iter())
    }
}

trait CmdLineProg {
    fn stdout(&self) -> String;
    fn stderr(&self) -> String;
}

pub trait ExitCode : fmt::Display {
    fn exit_code(&self) -> i8;
}

pub enum ServiceStatus {
    Ok,
    Warning,
    Critical,
    Unknown,
}

impl fmt::Display for ServiceStatus {
    /// It's conventional in the land of Nagios and its branches to write state codes in uppercase.
    /// `fmt()` follows that convention.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let uppercase_status = match self {
            ServiceStatus::Ok => "OK",
            ServiceStatus::Warning => "WARNING",
            ServiceStatus::Critical => "CRITICAL",
            ServiceStatus::Unknown => "UNKNOWN",
        };
        write!(f, "{}", uppercase_status)
    }
}

impl From<Datum> for ServiceStatus {
    fn from(datum: Datum) -> Self {
        if datum.is_crit() {
            ServiceStatus::Critical
        } else if datum.is_warn() {
            ServiceStatus::Warning
        } else {
            ServiceStatus::Ok
        }
    }
}

impl<'a> From<&Data<'a>> for ServiceStatus {
    fn from(data: &Data) -> Self {
        if data.is_unknown() {
            ServiceStatus::Unknown
        } else if data.any_crit() {
            ServiceStatus::Critical
        } else if data.any_warn() {
            ServiceStatus::Warning
        } else {
            ServiceStatus::Ok
        }
    }
}

impl ExitCode for Datum {
    fn exit_code(&self) -> i8 {
        if self.is_crit() {
            2
        } else if self.is_warn() {
            1
        } else {
            0
        }
    }
}

/*
impl<'a> ExitCode for Data<'a> {
    fn exit_code(&self) -> i8 {
        if self.is_unknown() {
            3
        } else if self.any_crit() {
            2
        } else if self.any_warn() {
            1
        } else {
            0
        }
    }
}
*/

impl ExitCode for ServiceStatus {
    fn exit_code(&self) -> i8 {
        match self {
            ServiceStatus::Ok => 0,
            ServiceStatus::Warning => 1,
            ServiceStatus::Critical => 2,
            ServiceStatus::Unknown => 3,
        }
    }
}

/// Host status determination is slightly less straightforward in Icinga 2 and Nagios than is
/// service status determination.
///
/// The first complication is that hosts (besides `Up` an `Down`) have the additional status of
/// `Unreachable`. A host is `Unreachable` when one of the hosts on which it depends is `Down` or
/// also `Unreachable`.
///
/// Then there's the fact that Icinga 2 simply treats plugin exit codes of `1` (which for a service
/// would be interpreted as `ServiceStatus::Warning`) as `HostStatus::Up`, while in Nagios, this
/// depends on the `use_aggressive_host_checking` option. When `use_aggressive_host_checking` is
/// enabled, an exit code of `1` will result not in `Up`, but in `Down` or `Unreachable`. Icinga 2
/// has no such `use_aggressive_host_checking` setting or equivalent and simply treats exit codes
/// of `1` as `HostStatus::Up`. `HostStatus::Upish` exists to retain the distinction between an
/// `HostStatus::Up` acquired from an exit code of `0` and a `HostStatus::Upish` acquired from an
/// exit code of `1`.
// TODO: Get rid of `Upis` and `Unreachable`?
pub enum HostStatus {
    Up,
    Upish,
    Down,
    Unreachable,
}

impl fmt::Display for HostStatus {
    /// It's conventional in the land of Nagios and its branches to write state codes in uppercase.
    /// `fmt()` follows that convention.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let uppercase_status = match self {
            HostStatus::Up => "UP",
            HostStatus::Upish => "UP",
            HostStatus::Down => "DOWN",
            HostStatus::Unreachable => "UNREACHABLE",
        };
        write!(f, "{}", uppercase_status)
    }
}

impl From<Datum> for HostStatus {
    fn from(datum: Datum) -> Self {
        if datum.is_crit() {
            HostStatus::Down
        } else {
            HostStatus::Up
        }
    }
}

impl<'a> From<&Data<'a>> for HostStatus {
    fn from(data: &Data) -> Self {
        if data.all_ok() {
            HostStatus::Up
        } else {
            HostStatus::Down
        }
    }
}

impl From<&ServiceStatus> for HostStatus {
    fn from(status: &ServiceStatus) -> Self {
        match status {
            ServiceStatus::Ok => Self::Up,
            ServiceStatus::Warning => Self::Up,
            ServiceStatus::Critical => Self::Down,
            ServiceStatus::Unknown => Self::Down,
        }
    }
}

impl ExitCode for HostStatus {
    //! `HostStatus::exit_code()` simplifies the actual Nagios/monitoring plugin behaviour
    //! a bit.
    fn exit_code(&self) -> i8 {
        match self {
            HostStatus::Up => 0,
            HostStatus::Upish => 1,
            HostStatus::Down => 2,
            HostStatus::Unreachable => 2,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_val_from_str() {
        assert_eq!(Value::from_str("U").unwrap(), Value(None));
        assert_eq!(Value::from_str("15").unwrap(), Value(Some(15.0)));
        assert_eq!(Value::from_str("12.45").unwrap(), Value(Some(12.45)));
        assert_eq!(Value::from_str("-1000").unwrap(), Value(Some(-1000.0)));
    }

    #[test]
    fn test_val_fmt() {
        assert_eq!(format!("{}", Value(None)), "U");
        assert_eq!(format!("{}", Value(Some(-12.4))), "-12.4");
        assert_eq!(format!("{}", Value(Some(12.4))), "12.4");
    }

    #[test]
    fn test_unit_from_str() {
        assert_eq!(Unit::from_str("").unwrap(), Unit::None);
        assert_eq!(Unit::from_str("s").unwrap(), Unit::Seconds);
    }

    #[test]
    fn test_unit_fmt() {
        assert_eq!(format!("{}", Unit::None), "");
        assert_eq!(format!("{}", Unit::Milliseconds), "ms");
    }

    #[test]
    fn test_min_from_str() {
        assert_eq!(Min::from_str("").unwrap(), Min(f32::NEG_INFINITY));
        assert_eq!(Min::from_str("-10").unwrap(), Min(-10.0));
        assert_eq!(Min::from_str("10").unwrap(), Min(10.0));
    }

    #[test]
    fn test_max_from_str() {
        assert_eq!(Max::from_str("").unwrap(), Max(f32::INFINITY));
        assert_eq!(Max::from_str("-10").unwrap(), Max(-10.0));
        assert_eq!(Max::from_str("10").unwrap(), Max(10.0));
    }

    /// Test the consistency checking of the `Range::new()` associated function.
    #[test]
    fn test_range_new() {
        assert!(Range::new(0.0, 10.0, true).is_ok());
        assert!(Range::new(-100.0, 0.0, true).is_ok());
        assert!(Range::new(100.0, -100.0, true).is_err());
        assert!(Range::new(f32::NEG_INFINITY, 0.0, true).is_ok());
        assert!(Range::new(0.0, f32::INFINITY, true).is_ok());
    }

    #[test]
    fn test_range_fmt() {
        assert_eq!(format!("{}", Range::new(0.0, f32::INFINITY, true).unwrap()), "");
        assert_eq!(format!("{}", Range::new(f32::NEG_INFINITY, f32::INFINITY, true).unwrap()), "~:");
        assert_eq!(format!("{}", Range::new(0.0, 840.0, true).unwrap()), "840");
        assert_eq!(format!("{}", Range::new(-840.0, 0.0, true).unwrap()), "-840:0");
        assert_eq!(format!("{}", Range::new(0.0, 1000.1, true).unwrap()), "1000.1");
        assert_eq!(format!("{}", Range::new(10.0, 20.0, false).unwrap()), "@10:20");
    }

    #[test]
    fn test_range_from_str() {
        assert_eq!(Range::from_str("").unwrap(), Range::new(0.0, f32::INFINITY, true).unwrap());
        assert_eq!(Range::from_str("~:").unwrap(), Range::new(f32::NEG_INFINITY, f32::INFINITY, true).unwrap());
        assert_eq!(Range::from_str("220").unwrap(), Range::new(0.0, 220.0, true).unwrap());
        assert_eq!(Range::from_str("-220:").unwrap(), Range::new(-220.0, f32::INFINITY, true).unwrap());
        assert_eq!(Range::from_str("1000.10").unwrap(), Range::new(0.0, 1000.10, true).unwrap());
        assert_eq!(Range::from_str("10").unwrap(), Range::new(0.0, 10.0, true).unwrap());
        assert_eq!(Range::from_str("@10").unwrap(), Range::new(0.0, 10.0, false).unwrap());
    }

    #[test]
    fn test_value_ok_within_range() {
        assert!(
            Range::new(0.0, 112.0, true).unwrap().is_value_ok(&Value(Some(100.0))),
            "100 falls between 0 and 112 and should be ok."
        );
        assert!(
            Range::new(0.0, 112.0, true).unwrap().is_value_ok(&Value(Some(112.0))),
            "Ranges are inclusive of their boundaries, and thus 112 should be ok."
        );
        assert!(
            !Range::new(0.0, 112.0, true).unwrap().is_value_ok(&Value(Some(112.01))),
            "112.01 > 112 and should not be ok."
        );
        assert!(
            Range::new(12.0, 112.0, true).unwrap().is_value_ok(&Value(Some(12.0))),
            "Ranges are inclusive of their boundaries, and thus 12 should be ok."
        );
        assert!(
            !Range::new(0.0, 112.0, true).unwrap().is_value_ok(&Value(Some(-0.01))),
            "0.01 < 0 and should not be ok."
        );
    }

    #[test]
    fn test_value_ok_outside_range() {
        assert!(
            Range::new(2000.0, 3000.0, false).unwrap().is_value_ok(&Value(Some(3001.0))),
            "3001 falls outside 2000 and 3000 and should be ok."
        );
        assert!(
            !Range::new(2000.0, 3000.0, false).unwrap().is_value_ok(&Value(Some(3000.0))),
            "Ranges are inclusive of their boundaries; 3000 should fall within the not-ok range."
        );
        assert!(
            !Range::new(2000.0, 3000.0, false).unwrap().is_value_ok(&Value(Some(2000.0))),
            "Ranges are inclusive of their boundaries; 2000 should fall within the not-ok range."
        );
    }

    #[test]
    fn test_perfdatum_from_str() {
        assert_eq!(Datum::from_str("metric=120;120;130;0;200").unwrap(), Datum {
            label: String::from("metric"),
            value: Value(Some(120.0)),
            unit: Unit::None,
            min: Min(0.0),
            max: Max(200.0),
            warn: Range::new(0.0, 120.0, true).ok(),
            crit: Range::new(0.0, 130.0, true).ok(),
        });
        assert_eq!(Datum::from_str("metric=120s;120;130;0;200").unwrap(), Datum {
            label: String::from("metric"),
            value: Value(Some(120.0)),
            unit: Unit::Seconds,
            min: Min(0.0),
            max: Max(200.0),
            warn: Range::new(0.0, 120.0, true).ok(),
            crit: Range::new(0.0, 130.0, true).ok(),
        });
        assert_eq!(Datum::from_str("metric=120;;;;").unwrap(), Datum {
            label: String::from("metric"),
            value: Value(Some(120.0)),
            unit: Unit::None,
            min: Min(f32::NEG_INFINITY),
            max: Max(f32::INFINITY),
            warn: None,
            crit: None,
        });
        assert_eq!(Datum::from_str("'spacy metric'=500ms").unwrap(), Datum {
            label: String::from("spacy metric"),
            value: Value(Some(500.0)),
            unit: Unit::Milliseconds,
            min: Min(f32::NEG_INFINITY),
            max: Max(f32::INFINITY),
            warn: None,
            crit: None,
        });
    }

    #[test]
    #[should_panic]
    fn test_perfdatum_from_str_unclosed_quotes() {
        Datum::from_str("'unclosed quotes=-100").unwrap();
    }

    #[test]
    fn test_perfdatum_fmt() {
        assert_eq!(
            format!("{}", Datum {
                label: String::from("metric"),
                value: Value(Some(120.0)),
                unit: Unit::None,
                min: Min(0.0),
                max: Max(200.0),
                warn: Range::new(0.0, 120.0, true).ok(),
                crit: Range::new(0.0, 130.0, true).ok(),
            }),
            "'metric'=120;120;130;0;200",
        );
        assert_eq!(
            format!("{}", Datum {
                label: String::from("metric"),
                value: Value(Some(120.0)),
                unit: Unit::Milliseconds,
                min: Min(0.0),
                max: Max(200.0),
                warn: Range::new(0.0, 120.0, true).ok(),
                crit: Range::new(0.0, 130.0, true).ok(),
            }),
            "'metric'=120ms;120;130;0;200",
        );
    }

    #[test]
    fn test_value_to_unit_without_si_prefix() {
        assert_eq!(
            value_to_unit_without_si_prefix(&Value(Some(18.0)), Unit::Bytes),
            (Value(Some(18.0)), Unit::Bytes)
        );
        assert_eq!(
            value_to_unit_without_si_prefix(&Value(Some(18.0)), Unit::Kilobytes),
            (Value(Some(18000.0)), Unit::Bytes)
        );
        assert_eq!(
            value_to_unit_without_si_prefix(&Value(Some(18.0)), Unit::Megabytes),
            (Value(Some(18000000.0)), Unit::Bytes)
        );
        assert_eq!(
            value_to_unit_without_si_prefix(&Value(None), Unit::Megabytes),
            (Value(None), Unit::Bytes)
        );
    }

    fn _test_datum_is_outside_range(range_type: RangeType) {
        let (warn_range, crit_range, is_bad): (Option<Range>, Option<Range>, fn(&Datum) -> bool) = match range_type {
            RangeType::Warn => (Some(Range::new(100.0, 120.0, true).unwrap()), None, Datum::is_warn),
            RangeType::Crit => (None, Some(Range::new(100.0, 120.0, true).unwrap()), Datum::is_crit),
        };

        let too_low = Datum {
            label: String::from("metric"),
            value: Value(Some(99.0)),
            unit: Unit::None,
            min: Min(0.0),
            max: Max(f32::INFINITY),
            warn: warn_range,
            crit: crit_range,
        };
        assert!(is_bad(&too_low));

        let almost_too_low = Datum {
            label: String::from("metric"),
            value: Value(Some(100.0)),
            unit: Unit::None,
            min: Min(0.0),
            max: Max(f32::INFINITY),
            warn: warn_range,
            crit: crit_range,
        };
        assert!(!is_bad(&almost_too_low));

        let almost_too_high = Datum {
            label: String::from("metric"),
            value: Value(Some(120.0)),
            unit: Unit::None,
            min: Min(0.0),
            max: Max(f32::INFINITY),
            warn: warn_range,
            crit: crit_range,
        };
        assert!(!is_bad(&almost_too_high));

        let too_high = Datum {
            label: String::from("metric"),
            value: Value(Some(121.12)),
            unit: Unit::Milliseconds,
            min: Min(0.0),
            max: Max(200.0),
            warn: warn_range,
            crit: crit_range,
        };
        assert!(is_bad(&too_high));
    }

    #[test]
    fn test_datum_is_warn_outside_range() {
        _test_datum_is_outside_range(RangeType::Warn);
    }

    #[test]
    fn test_datum_is_crit_outside_range() {
        _test_datum_is_outside_range(RangeType::Crit);
    }

    fn _test_datum_is_inside_range(range_type: RangeType) {
        let (warn_range, crit_range, is_bad): (Option<Range>, Option<Range>, fn(&Datum) -> bool) = match range_type {
            RangeType::Warn => (Some(Range::new(8.0, 10.0, false).unwrap()), None, Datum::is_warn),
            RangeType::Crit => (None, Some(Range::new(8.0, 10.0, false).unwrap()), Datum::is_crit),
        };

        let low_enough = Datum {
            label: String::from("metric"),
            value: Value(Some(7.999)),
            unit: Unit::None,
            min: Min(0.0),
            max: Max(f32::INFINITY),
            warn: warn_range,
            crit: crit_range,
        };
        assert!(!is_bad(&low_enough));

        let just_within_warn_range = Datum {
            label: String::from("metric"),
            value: Value(Some(8.0)),
            unit: Unit::None,
            min: Min(0.0),
            max: Max(f32::INFINITY),
            warn: warn_range,
            crit: crit_range,
        };
        assert!(is_bad(&just_within_warn_range));

        let still_within_warn = Datum {
            label: String::from("metric"),
            value: Value(Some(10.0)),
            unit: Unit::None,
            min: Min(0.0),
            max: Max(f32::INFINITY),
            warn: warn_range,
            crit: crit_range,
        };
        assert!(is_bad(&still_within_warn));

        let high_enough = Datum {
            label: String::from("metric"),
            value: Value(Some(10.1)),
            unit: Unit::Milliseconds,
            min: Min(0.0),
            max: Max(200.0),
            warn: warn_range,
            crit: crit_range,
        };
        assert!(!is_bad(&high_enough));
    }

    #[test]
    fn test_datum_is_warn_inside_range() {
        _test_datum_is_inside_range(RangeType::Warn);
    }

    #[test]
    fn test_datum_is_crit_inside_range() {
        _test_datum_is_inside_range(RangeType::Crit);
    }

    #[test]
    fn test_datum_is_not_ok() {
        let too_low = Datum {
            label: String::from("metric"),
            value: Value(Some(99.99)),
            unit: Unit::Milliseconds,
            min: Min(0.0),
            max: Max(200.0),
            warn: Range::new(100.0, 120.0, true).ok(),
            crit: Range::new(100.0, 130.0, true).ok(),
        };
        assert!(too_low.is_not_ok());
    }

    #[test]
    fn test_datum_is_ok() {
        let good = Datum {
            label: String::from("metric"),
            value: Value(Some(110.0)),
            unit: Unit::Milliseconds,
            min: Min(0.0),
            max: Max(200.0),
            warn: Range::new(100.0, 120.0, true).ok(),
            crit: Range::new(100.0, 130.0, true).ok(),
        };
        assert!(good.is_ok());
    }

    #[test]
    fn test_data_label_1st_19_chars_must_be_distinct() {
        let mut data = Data::new();
        assert!(data.add_distinct(Datum {
            label: String::from("i am a unique label"),  // … and exactly 19 characters long
            value: Value(None),
            unit: Unit::None,
            min: Min(f32::NEG_INFINITY),
            max: Max(f32::INFINITY),
            warn: None,
            crit: None,
        }).is_ok());

        assert!(data.add_distinct(Datum {
            label: String::from("i am a unique label too"),  // … except that the 1st 19 chars are not!
            value: Value(None),
            unit: Unit::None,
            min: Min(f32::NEG_INFINITY),
            max: Max(f32::INFINITY),
            warn: None,
            crit: None,
        }).is_err());

        assert!(data.add_distinct(Datum {
            label: String::from("my 1st 19 chars are distinct"),  // … except that the 1st 19 chars are not!
            value: Value(None),
            unit: Unit::None,
            min: Min(f32::NEG_INFINITY),
            max: Max(f32::INFINITY),
            warn: None,
            crit: None,
        }).is_ok());
    }

    #[test]
    fn test_data_iterator() {
        let mut data = Data::new();
        data.add_distinct(Datum {
            label: String::from("metric1"),
            value: Value(Some(0.1)),
            unit: Unit::Seconds,
            min: Min(f32::NEG_INFINITY),
            max: Max(f32::INFINITY),
            warn: None,
            crit: None,
        });
        data.add_distinct(Datum {
            label: String::from("metric2"),
            value: Value(Some(2.0)),
            unit: Unit::Megabytes,
            min: Min(f32::NEG_INFINITY),
            max: Max(f32::INFINITY),
            warn: None,
            crit: None,
        });
        let mut iterator = data.into_iter();
        assert_eq!(iterator.next().unwrap().label, String::from("metric1"));
    }

    #[test]
    fn test_data_from_str() {
        let data = Data::from_str(r"OK | response_time=100ms
More stuff.
And more.
Even more.
| perf_datum1=12%;80;90
perf_datum2=12%;80;90").unwrap();
        let mut iter = data.into_iter();
        assert_eq!(iter.next().unwrap(), &Datum {
            label: String::from("response_time"),
            value: Value(Some(100.0)),
            unit: Unit::Milliseconds,
            min: Min(f32::NEG_INFINITY),
            max: Max(f32::INFINITY),
            warn: None,
            crit: None,
        });
        assert_eq!(iter.next().unwrap(), &Datum {
            label: String::from("perf_datum1"),
            value: Value(Some(12.0)),
            unit: Unit::Percentage,
            min: Min(0.0),
            max: Max(100.0),
            warn: Range::new(0.0, 80.0, true).ok(),
            crit: Range::new(0.0, 90.0, true).ok(),
        });

        let data = Data::from_str(r"line1=12%;80;90
line2=22%;70;99").unwrap();
        let mut iter = data.into_iter();
        assert_eq!(iter.next().unwrap(), &Datum {
            label: String::from("line1"),
            value: Value(Some(12.0)),
            unit: Unit::Percentage,
            min: Min(0.0),
            max: Max(100.0),
            warn: Range::new(0.0, 80.0, true).ok(),
            crit: Range::new(0.0, 90.0, true).ok(),
        });
        assert_eq!(iter.next().unwrap(), &Datum {
            label: String::from("line2"),
            value: Value(Some(22.0)),
            unit: Unit::Percentage,
            min: Min(0.0),
            max: Max(100.0),
            warn: Range::new(0.0, 70.0, true).ok(),
            crit: Range::new(0.0, 99.0, true).ok(),
        });
    }
}
