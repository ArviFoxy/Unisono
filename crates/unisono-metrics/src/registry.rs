// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! The owner of the metric families, and their export.

use std::error::Error;
use std::fmt::{self, Display, Formatter, Write};
use std::io;
use std::sync::Arc;

use crate::counter::Counter;
use crate::gauge::{FloatGauge, Gauge};
use crate::histogram::{Buckets, Histogram};
use crate::text::{self, Braced, Number};

/// Why a family or a series was not registered.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RegistrationError {
    /// The metric name is not of the form `[a-zA-Z_:][a-zA-Z0-9_:]*`.
    MetricName,
    /// A label name is not of the form `[a-zA-Z_][a-zA-Z0-9_]*`, begins with
    /// `__`, occurs twice, or is `le` in a histogram, where the format uses
    /// that name for the bounds of the buckets.
    LabelName,
    /// Another family already writes sample lines under the name, or, for a
    /// histogram, under one of its names with `_bucket`, `_sum` or `_count`
    /// appended.
    NameTaken,
    /// A family of this name exists with another help text, type, list of
    /// label names or buckets.
    Conflict,
    /// The histogram has no steps in a unit, or the bounds of its buckets do
    /// not increase strictly as exported.
    Buckets,
    /// The number of label values is not the number of label names of the
    /// family.
    LabelCount,
    /// The family is not a family of this registry.
    UnknownFamily,
}

impl Display for RegistrationError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::MetricName => "the metric name is not a valid name",
            Self::LabelName => "a label name is not valid, is reserved or occurs twice",
            Self::NameTaken => "another family already uses a name of this family",
            Self::Conflict => "a family of this name exists with another definition",
            Self::Buckets => "the buckets have no steps in a unit or bounds that do not increase",
            Self::LabelCount => "the number of label values is not the number of label names",
            Self::UnknownFamily => "the family is not a family of this registry",
        })
    }
}

impl Error for RegistrationError {}

/// A family of counters in a [`Registry`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CounterFamily(usize);

/// A family of integer gauges in a [`Registry`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GaugeFamily(usize);

/// A family of floating-point gauges in a [`Registry`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FloatGaugeFamily(usize);

/// A family of histograms in a [`Registry`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HistogramFamily(usize);

/// What the series of a family are.
#[derive(Debug, PartialEq)]
enum Kind {
    Counter,
    Gauge,
    FloatGauge,
    Histogram(Arc<Buckets>),
}

impl Kind {
    /// The word of the `# TYPE` line.
    fn type_name(&self) -> &'static str {
        match self {
            Kind::Counter => "counter",
            Kind::Gauge | Kind::FloatGauge => "gauge",
            Kind::Histogram(_) => "histogram",
        }
    }

    /// The names that a family called `name` writes lines under.
    fn line_names(&self, name: &str) -> Vec<String> {
        let suffixes: &[&str] = match self {
            Kind::Histogram(_) => &["", "_bucket", "_sum", "_count"],
            _ => &[""],
        };
        suffixes
            .iter()
            .map(|suffix| format!("{name}{suffix}"))
            .collect()
    }

    /// A new series, at zero.
    fn series(&self) -> Series {
        match self {
            Kind::Counter => Series::Counter(Counter::new()),
            Kind::Gauge => Series::Gauge(Gauge::new()),
            Kind::FloatGauge => Series::FloatGauge(FloatGauge::new()),
            Kind::Histogram(buckets) => Series::Histogram(Histogram::new(buckets)),
        }
    }
}

/// The registry's own handle to a series.
#[derive(Clone, Debug)]
enum Series {
    Counter(Counter),
    Gauge(Gauge),
    FloatGauge(FloatGauge),
    Histogram(Histogram),
}

#[derive(Debug)]
struct Family {
    name: Box<str>,
    help: Box<str>,
    label_names: Box<[Box<str>]>,
    kind: Kind,
    /// The `# HELP` and `# TYPE` lines.
    header: Box<str>,
    /// Every series with its labels as a sample line carries them, without
    /// braces.
    series: Vec<(Box<str>, Series)>,
}

/// The metric families of a program, and their series.
///
/// Registering takes `&mut self` and exporting `&self`: the registry has no
/// lock. A program that registers series while another thread exports puts
/// the registry behind a lock of its own. The threads that update series
/// hold handles and never touch the registry.
///
/// The registry holds a handle to every series, so a thread that drops its
/// handle frees no memory as long as the registry lives.
#[derive(Debug, Default)]
pub struct Registry {
    families: Vec<Family>,
}

impl Registry {
    /// A registry without families.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Registers a family of counters.
    ///
    /// Registering a family again, with the same help text and label names,
    /// gives the family that exists.
    ///
    /// # Errors
    ///
    /// [`MetricName`], [`LabelName`], [`NameTaken`] or [`Conflict`].
    ///
    /// [`MetricName`]: RegistrationError::MetricName
    /// [`LabelName`]: RegistrationError::LabelName
    /// [`NameTaken`]: RegistrationError::NameTaken
    /// [`Conflict`]: RegistrationError::Conflict
    pub fn counter_family(
        &mut self,
        name: &str,
        help: &str,
        label_names: &[&str],
    ) -> Result<CounterFamily, RegistrationError> {
        self.family(name, help, label_names, Kind::Counter)
            .map(CounterFamily)
    }

    /// Registers a family of integer gauges.
    ///
    /// Registering a family again, with the same help text and label names,
    /// gives the family that exists.
    ///
    /// # Errors
    ///
    /// [`MetricName`], [`LabelName`], [`NameTaken`] or [`Conflict`].
    ///
    /// [`MetricName`]: RegistrationError::MetricName
    /// [`LabelName`]: RegistrationError::LabelName
    /// [`NameTaken`]: RegistrationError::NameTaken
    /// [`Conflict`]: RegistrationError::Conflict
    pub fn gauge_family(
        &mut self,
        name: &str,
        help: &str,
        label_names: &[&str],
    ) -> Result<GaugeFamily, RegistrationError> {
        self.family(name, help, label_names, Kind::Gauge)
            .map(GaugeFamily)
    }

    /// Registers a family of floating-point gauges.
    ///
    /// Registering a family again, with the same help text and label names,
    /// gives the family that exists.
    ///
    /// # Errors
    ///
    /// [`MetricName`], [`LabelName`], [`NameTaken`] or [`Conflict`].
    ///
    /// [`MetricName`]: RegistrationError::MetricName
    /// [`LabelName`]: RegistrationError::LabelName
    /// [`NameTaken`]: RegistrationError::NameTaken
    /// [`Conflict`]: RegistrationError::Conflict
    pub fn float_gauge_family(
        &mut self,
        name: &str,
        help: &str,
        label_names: &[&str],
    ) -> Result<FloatGaugeFamily, RegistrationError> {
        self.family(name, help, label_names, Kind::FloatGauge)
            .map(FloatGaugeFamily)
    }

    /// Registers a family of histograms.
    ///
    /// The histograms count whole numbers of steps, `steps_per_unit` of which
    /// make one unit of the exported value. `bounds` are the upper bounds of
    /// the buckets in steps, in increasing order; a bucket for the values
    /// above the last bound is added. A value equal to a bound belongs to
    /// that bound's bucket.
    ///
    /// Registering a family again, with the same help text, label names and
    /// buckets, gives the family that exists.
    ///
    /// # Errors
    ///
    /// [`MetricName`], [`LabelName`], [`NameTaken`], [`Conflict`] or
    /// [`Buckets`].
    ///
    /// [`MetricName`]: RegistrationError::MetricName
    /// [`LabelName`]: RegistrationError::LabelName
    /// [`NameTaken`]: RegistrationError::NameTaken
    /// [`Conflict`]: RegistrationError::Conflict
    /// [`Buckets`]: RegistrationError::Buckets
    pub fn histogram_family(
        &mut self,
        name: &str,
        help: &str,
        label_names: &[&str],
        bounds: &[i64],
        steps_per_unit: u64,
    ) -> Result<HistogramFamily, RegistrationError> {
        let buckets = Buckets::new(bounds, steps_per_unit).ok_or(RegistrationError::Buckets)?;
        self.family(name, help, label_names, Kind::Histogram(Arc::new(buckets)))
            .map(HistogramFamily)
    }

    /// The counter of `family` with the given label values, one for each
    /// label name of the family in their order. It is registered at zero if
    /// the family has no such counter yet.
    ///
    /// # Errors
    ///
    /// [`LabelCount`] or [`UnknownFamily`].
    ///
    /// [`LabelCount`]: RegistrationError::LabelCount
    /// [`UnknownFamily`]: RegistrationError::UnknownFamily
    pub fn counter(
        &mut self,
        family: CounterFamily,
        label_values: &[&str],
    ) -> Result<Counter, RegistrationError> {
        match self.series(family.0, label_values, |kind| matches!(kind, Kind::Counter))? {
            Series::Counter(counter) => Ok(counter),
            _ => Err(RegistrationError::UnknownFamily),
        }
    }

    /// The integer gauge of `family` with the given label values, one for
    /// each label name of the family in their order. It is registered at
    /// zero if the family has no such gauge yet.
    ///
    /// # Errors
    ///
    /// [`LabelCount`] or [`UnknownFamily`].
    ///
    /// [`LabelCount`]: RegistrationError::LabelCount
    /// [`UnknownFamily`]: RegistrationError::UnknownFamily
    pub fn gauge(
        &mut self,
        family: GaugeFamily,
        label_values: &[&str],
    ) -> Result<Gauge, RegistrationError> {
        match self.series(family.0, label_values, |kind| matches!(kind, Kind::Gauge))? {
            Series::Gauge(gauge) => Ok(gauge),
            _ => Err(RegistrationError::UnknownFamily),
        }
    }

    /// The floating-point gauge of `family` with the given label values, one
    /// for each label name of the family in their order. It is registered at
    /// zero if the family has no such gauge yet.
    ///
    /// # Errors
    ///
    /// [`LabelCount`] or [`UnknownFamily`].
    ///
    /// [`LabelCount`]: RegistrationError::LabelCount
    /// [`UnknownFamily`]: RegistrationError::UnknownFamily
    pub fn float_gauge(
        &mut self,
        family: FloatGaugeFamily,
        label_values: &[&str],
    ) -> Result<FloatGauge, RegistrationError> {
        match self.series(family.0, label_values, |kind| {
            matches!(kind, Kind::FloatGauge)
        })? {
            Series::FloatGauge(gauge) => Ok(gauge),
            _ => Err(RegistrationError::UnknownFamily),
        }
    }

    /// The histogram of `family` with the given label values, one for each
    /// label name of the family in their order. It is registered empty if
    /// the family has no such histogram yet.
    ///
    /// # Errors
    ///
    /// [`LabelCount`] or [`UnknownFamily`].
    ///
    /// [`LabelCount`]: RegistrationError::LabelCount
    /// [`UnknownFamily`]: RegistrationError::UnknownFamily
    pub fn histogram(
        &mut self,
        family: HistogramFamily,
        label_values: &[&str],
    ) -> Result<Histogram, RegistrationError> {
        match self.series(family.0, label_values, |kind| {
            matches!(kind, Kind::Histogram(_))
        })? {
            Series::Histogram(histogram) => Ok(histogram),
            _ => Err(RegistrationError::UnknownFamily),
        }
    }

    /// Writes every family in the Prometheus text format, version 0.0.4.
    ///
    /// The crate's documentation says what a reader of the text may rely on
    /// while other threads update.
    ///
    /// # Errors
    ///
    /// The error of `out`.
    pub fn write_text<W: Write>(&self, out: &mut W) -> fmt::Result {
        for family in &self.families {
            out.write_str(&family.header)?;
            for (labels, series) in &family.series {
                let name = &family.name;
                let braced = Braced(labels);
                match series {
                    Series::Counter(counter) => writeln!(out, "{name}{braced} {}", counter.get())?,
                    Series::Gauge(gauge) => writeln!(out, "{name}{braced} {}", gauge.get())?,
                    Series::FloatGauge(gauge) => {
                        writeln!(out, "{name}{braced} {}", Number(gauge.get()))?;
                    }
                    Series::Histogram(histogram) => histogram.write(out, name, labels)?,
                }
            }
        }
        Ok(())
    }

    /// Writes what [`write_text`] writes, as bytes.
    ///
    /// The text goes to `out` in many small pieces, so a socket or a file is
    /// best wrapped in a buffer.
    ///
    /// # Errors
    ///
    /// The error of `out`.
    ///
    /// [`write_text`]: Registry::write_text
    pub fn write_text_io<W: io::Write>(&self, out: &mut W) -> io::Result<()> {
        write!(out, "{}", Text(self))
    }

    /// The place of the family with this definition, which is registered if
    /// no family has the name yet.
    fn family(
        &mut self,
        name: &str,
        help: &str,
        label_names: &[&str],
        kind: Kind,
    ) -> Result<usize, RegistrationError> {
        if !text::is_metric_name(name) {
            return Err(RegistrationError::MetricName);
        }
        for (place, label) in label_names.iter().enumerate() {
            let bound_label = matches!(kind, Kind::Histogram(_)) && *label == "le";
            let repeated = label_names.iter().take(place).any(|other| other == label);
            if !text::is_label_name(label) || bound_label || repeated {
                return Err(RegistrationError::LabelName);
            }
        }
        if let Some((place, family)) = self
            .families
            .iter()
            .enumerate()
            .find(|(_, family)| *family.name == *name)
        {
            let same = *family.help == *help
                && family.kind == kind
                && family
                    .label_names
                    .iter()
                    .map(|label| &**label)
                    .eq(label_names.iter().copied());
            return if same {
                Ok(place)
            } else {
                Err(RegistrationError::Conflict)
            };
        }
        let line_names = kind.line_names(name);
        let taken = self.families.iter().any(|family| {
            family
                .kind
                .line_names(&family.name)
                .iter()
                .any(|theirs| line_names.contains(theirs))
        });
        if taken {
            return Err(RegistrationError::NameTaken);
        }
        let mut escaped_help = String::new();
        text::push_help(&mut escaped_help, help);
        let header = format!(
            "# HELP {name} {escaped_help}\n# TYPE {name} {}\n",
            kind.type_name()
        );
        self.families.push(Family {
            name: name.into(),
            help: help.into(),
            label_names: label_names.iter().map(|label| (*label).into()).collect(),
            kind,
            header: header.into(),
            series: Vec::new(),
        });
        Ok(self.families.len() - 1)
    }

    /// The registry's handle to the series of a family with these label
    /// values, which is registered if the family has none yet. The family
    /// must be of the kind that `expected` accepts.
    fn series(
        &mut self,
        family: usize,
        label_values: &[&str],
        expected: fn(&Kind) -> bool,
    ) -> Result<Series, RegistrationError> {
        let family = self
            .families
            .get_mut(family)
            .filter(|family| expected(&family.kind))
            .ok_or(RegistrationError::UnknownFamily)?;
        if label_values.len() != family.label_names.len() {
            return Err(RegistrationError::LabelCount);
        }
        let mut labels = String::new();
        for (name, value) in family.label_names.iter().zip(label_values) {
            if !labels.is_empty() {
                labels.push(',');
            }
            labels.push_str(name);
            labels.push_str("=\"");
            text::push_label_value(&mut labels, value);
            labels.push('"');
        }
        // Escaping maps different values to different texts, so equal texts
        // mean equal label values.
        if let Some((_, series)) = family.series.iter().find(|(known, _)| **known == *labels) {
            return Ok(series.clone());
        }
        let series = family.kind.series();
        family.series.push((labels.into(), series.clone()));
        Ok(series)
    }
}

/// The text of a registry, for writers of bytes.
struct Text<'a>(&'a Registry);

impl Display for Text<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.0.write_text(f)
    }
}
