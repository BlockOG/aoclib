use std::{fmt, iter, ops::Index, slice};

/// A struct for handling and parsing an input for an Advent of Code problem.
#[derive(Clone, Copy, Debug)]
pub struct Input<'a> {
    raw: &'a str,
    lines: &'a [&'a str],
}

impl<'a> Input<'a> {
    pub(crate) fn new(raw: &'a str, lines: &'a [&'a str]) -> Self {
        Self { raw, lines }
    }

    /// Returns the raw input `&str`.
    #[inline(always)]
    pub fn raw(self) -> &'a str {
        self.raw
    }

    /// Returns an iterator over the lines of the input.
    ///
    /// Alias for `.into_iter()`.
    #[inline(always)]
    pub fn lines(self) -> Lines<'a> {
        self.into_iter()
    }

    /// Returns the lines of the input as a slice.
    #[inline(always)]
    pub fn as_lines(self) -> &'a [&'a str] {
        self.lines
    }

    /// Returns the number of lines in the input.
    #[inline(always)]
    #[allow(clippy::len_without_is_empty)] // Panics if the input is empty.
    pub fn len(self) -> usize {
        self.lines.len()
    }
}

/// An iterator over the lines of an `Input`.
#[derive(Clone)]
pub struct Lines<'a> {
    inner: slice::Iter<'a, &'a str>,
}

impl<'a> Iterator for Lines<'a> {
    type Item = &'a str;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().copied()
    }
}

impl<'a> DoubleEndedIterator for Lines<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back().copied()
    }
}

impl<'a> ExactSizeIterator for Lines<'a> {
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<'a> iter::FusedIterator for Lines<'a> {}

impl<'a> IntoIterator for Input<'a> {
    type Item = &'a str;
    type IntoIter = Lines<'a>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        Lines {
            inner: self.lines.iter(),
        }
    }
}

impl<'a, T> Index<T> for Input<'a>
where
    [&'a str]: Index<T>,
{
    type Output = <[&'a str] as Index<T>>::Output;

    #[inline]
    #[track_caller]
    fn index(&self, index: T) -> &Self::Output {
        &self.lines[index]
    }
}

impl<'a> fmt::Display for Input<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <str as fmt::Display>::fmt(self.raw, f)
    }
}
