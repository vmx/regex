// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::error;
use std::fmt;

/// An error that occurred while parsing a regular expression into an abstract
/// syntax tree.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AstError {
    /// The span of this error.
    pub span: Span,
    /// The kind of error.
    pub kind: AstErrorKind,
}

impl error::Error for AstError {
    fn description(&self) -> &str {
        use self::AstErrorKind::*;
        match self.kind {
            ClassIllegal => "illegal item found in character class",
            ClassUnclosed => "unclosed character class",
            CountedRepetitionUnclosed => "unclosed counted repetition",
            DecimalEmpty => "empty decimal literal",
            DecimalInvalid => "invalid decimal literal",
            EscapeHexEmpty => "empty hexadecimal literal",
            EscapeHexInvalid => "invalid hexadecimal literal",
            EscapeHexInvalidDigit{..} => "invalid hexadecimal digit",
            EscapeUnexpectedEof => "unexpected eof (escape sequence)",
            EscapeUnrecognized{..} => "unrecognized escape sequence",
            FlagDuplicate{..} => "duplicate flag",
            FlagRepeatedNegation{..} => "repeated negation",
            FlagUnexpectedEof => "unexpected eof (flag)",
            FlagUnrecognized{..} => "unrecognized flag",
            GroupEmpty => "empty group",
            GroupNameEmpty => "empty capture group name",
            GroupNameInvalid{..} => "invalid capture group name",
            GroupNameUnexpectedEof => "unclosed capture group name",
            GroupUnclosed => "unclosed group",
            GroupUnopened => "unopened group",
            NestLimitExceeded(_) => "nest limit exceeded",
        }
    }
}

impl fmt::Display for AstError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::AstErrorKind::*;
        match self.kind {
            ClassIllegal => {
                write!(f, "illegal item found in character class")
            }
            ClassUnclosed => {
                write!(f, "unclosed character class")
            }
            CountedRepetitionUnclosed => {
                write!(f, "unclosed counted repetition")
            }
            DecimalEmpty => {
                write!(f, "decimal literal empty")
            }
            DecimalInvalid => {
                write!(f, "decimal literal invalid")
            }
            EscapeHexEmpty => {
                write!(f, "hexadecimal literal empty")
            }
            EscapeHexInvalid => {
                write!(f, "hexadecimal literal is not a Unicode scalar value")
            }
            EscapeHexInvalidDigit { c } => {
                write!(f, "invalid hexadecimal digit '{}'", c)
            }
            EscapeUnexpectedEof => {
                write!(f, "incomplete escape sequence, \
                           reached end of pattern prematurely")
            }
            EscapeUnrecognized { c } => {
                write!(f, "unrecognized escape sequence '\\{}'", c)
            }
            FlagDuplicate { flag, .. } => {
                write!(f, "duplicate flag '{}'", flag)
            }
            FlagRepeatedNegation{..} => {
                write!(f, "flag negation operator repeated")
            }
            FlagUnexpectedEof => {
                write!(f, "expected flag but got end of regex")
            }
            FlagUnrecognized { flag } => {
                write!(f, "unrecognized flag '{}'", flag)
            }
            GroupEmpty => {
                write!(f, "empty group")
            }
            GroupNameEmpty => {
                write!(f, "empty capture group name")
            }
            GroupNameInvalid{ c } => {
                write!(f, "invalid capture group character '{}'", c)
            }
            GroupNameUnexpectedEof => {
                write!(f, "unclosed capture group name")
            }
            GroupUnclosed => {
                write!(f, "unclosed group")
            }
            GroupUnopened => {
                write!(f, "unopened group")
            }
            NestLimitExceeded(limit) => {
                write!(f, "exceed the maximum number of \
                           nested parentheses/brackets ({})", limit)
            }
        }
    }
}

// BREADCRUMBS: Figure out some convenient constructors. Perhaps write more
// parsing code first to get a better idea...

impl AstError {
}

/// The type of an error that occurred while building an AST.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AstErrorKind {
    /// An invalid escape sequence was found in a character class set.
    ClassIllegal,
    /// An opening `[` was found with no corresponding closing `]`.
    ClassUnclosed,
    /// An opening `{` was found with no corresponding closing `}`.
    CountedRepetitionUnclosed,
    /// An empty decimal number was given where one was expected.
    DecimalEmpty,
    /// An invalid decimal number was given where one was expected.
    DecimalInvalid,
    /// A bracketed hex literal was empty.
    EscapeHexEmpty,
    /// A bracketed hex literal did not correspond to a Unicode scalar value.
    EscapeHexInvalid,
    /// An invalid hexadecimal digit was found.
    EscapeHexInvalidDigit {
        /// The invalid digit (i.e., not [0-9a-zA-Z]).
        c: char,
    },
    /// EOF was found before an escape sequence was completed.
    EscapeUnexpectedEof,
    /// An unrecognized escape sequence.
    EscapeUnrecognized {
        /// The unrecognized escape.
        c: char,
    },
    /// A flag was used twice, e.g., `i-i`.
    FlagDuplicate {
        /// The duplicate flag.
        flag: char,
        /// The position of the original flag. The error position
        /// points to the duplicate flag.
        original: Span,
    },
    /// The negation operator was used twice, e.g., `-i-s`.
    FlagRepeatedNegation {
        /// The position of the original negation operator. The error position
        /// points to the duplicate negation operator.
        original: Span,
    },
    /// Expected a flag but got EOF, e.g., `(?`.
    FlagUnexpectedEof,
    /// Unrecognized flag, e.g., `a`.
    FlagUnrecognized {
        /// The unrecognized flag.
        flag: char,
    },
    /// An empty group, e.g., `()`.
    GroupEmpty,
    /// A capture group name is empty, e.g., `(?P<>abc)`.
    GroupNameEmpty,
    /// An invalid character was seen for a capture group name. This includes
    /// errors where the first character is a digit (even though subsequent
    /// characters are allowed to be digits).
    GroupNameInvalid {
        /// The invalid character. This may be a digit if it's the first
        /// character in the name.
        c: char,
    },
    /// A closing `>` could not be found for a capture group name.
    GroupNameUnexpectedEof,
    /// An unclosed group, e.g., `(ab`.
    ///
    /// The span of this error corresponds to the unclosed parenthesis.
    GroupUnclosed,
    /// An unopened group, e.g., `ab)`.
    GroupUnopened,
    /// The nest limit was exceeded. The limit stored here is the limit
    /// configured in the parser.
    NestLimitExceeded(u32),
}

/// Span represents the position information of a single AST item.
///
/// All span positions are absolute byte offsets that can be used on the
/// original regular expression that was parsed.
#[derive(Clone, Copy, Eq, PartialEq)]
pub struct Span {
    /// The start byte offset.
    pub start: Position,
    /// The end byte offset.
    pub end: Position,
}

impl fmt::Debug for Span {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Span({:?}, {:?})", self.start, self.end)
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub struct Position {
    /// The absolute offset of this position, starting at `0` from the
    /// beginning of the regular expression pattern string.
    pub offset: usize,
    /// The line number, starting at `1`.
    pub line: usize,
    /// The approximate column number, starting at `1`.
    pub column: usize,
}

impl fmt::Debug for Position {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Position(o: {:?}, l: {:?}, c: {:?})",
            self.offset, self.line, self.column)
    }
}

impl Span {
    /// Create a new span with the given positions.
    pub fn new(start: Position, end: Position) -> Span {
        Span { start: start, end: end }
    }

    /// Create a new span using the given position as the start and end.
    pub fn splat(pos: Position) -> Span {
        Span::new(pos, pos)
    }

    /// Create a new span by replacing the starting the position with the one
    /// given.
    pub fn with_start(self, pos: Position) -> Span {
        Span { start: pos, ..self }
    }

    /// Create a new span by replacing the ending the position with the one
    /// given.
    pub fn with_end(self, pos: Position) -> Span {
        Span { end: pos, ..self }
    }
}

impl Position {
    /// Create a new position with the given information.
    ///
    /// `offset` is the absolute offset of the position, starting at `0` from
    /// the beginning of the regular expression pattern string.
    ///
    /// `line` is the line number, starting at `1`.
    ///
    /// `column` is the approximate column number, starting at `1`.
    pub fn new(offset: usize, line: usize, column: usize) -> Position {
        Position { offset: offset, line: line, column: column }
    }
}

/// An abstract syntax tree for a singular expression along with comments
/// found.
///
/// Comments are not stored in the tree itself to avoid complexity. Each
/// comment contains a span of precisely where it occurred in the original
/// regular expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AstWithComments {
    /// The actual ast.
    pub ast: Ast,
    /// All comments found in the original regular expression.
    pub comments: Vec<AstComment>,
}

/// A comment from a regular expression with an associated span.
///
/// A regular expression can only contain comments when the `x` flag is
/// enabled.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AstComment {
    /// The span of this comment, including the beginning `#` and ending `\n`.
    pub span: Span,
    /// The comment text, starting with the first character following the `#`
    /// and ending with the last character preceding the `\n`.
    pub comment: String,
}

/// An abstract syntax tree for a single regular expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Ast {
    /// An empty regex that matches exactly the empty string.
    Empty(Span),
    /// A set of flags, e.g., `(?is)`.
    Flags(AstSetFlags),
    /// A single character literal, which includes escape sequences.
    Literal(AstLiteral),
    /// The "any character" class.
    Dot(Span),
    /// A single zero-width assertion.
    Assertion(AstAssertion),
    /// A single character class. This includes all forms of character classes
    /// except for `.`. e.g., `\d`, `\pN`, `[a-z]` and `[[:alpha:]]`.
    Class(AstClass),
    /// A repetition operator applied to an arbitrary regular expression.
    Repetition(AstRepetition),
    /// A grouped regular expression.
    Group(AstGroup),
    /// An alternation of regular expressions.
    Alternation(AstAlternation),
    /// A concatenation of regular expressions.
    Concat(AstConcat),
}

impl Ast {
    /// Return the span of this abstract syntax tree.
    pub fn span(&self) -> &Span {
        match *self {
            Ast::Empty(ref span) => span,
            Ast::Literal(ref x) => &x.span,
            Ast::Dot(ref span) => span,
            Ast::Class(ref x) => x.span(),
            Ast::Assertion(ref x) => &x.span,
            Ast::Repetition(ref x) => &x.span,
            Ast::Group(ref x) => &x.span,
            Ast::Flags(ref x) => &x.span,
            Ast::Alternation(ref x) => &x.span,
            Ast::Concat(ref x) => &x.span,
        }
    }
}

/// An alternation of regular expressions.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AstAlternation {
    /// The span of this alternation.
    pub span: Span,
    /// The alternate regular expressions.
    pub asts: Vec<Ast>,
}

impl AstAlternation {
    /// Return this alternation as an AST.
    ///
    /// If this alternation contains zero ASTs, then Ast::Empty is
    /// returned. If this alternation contains exactly 1 AST, then the
    /// corresponding AST is returned. Otherwise, Ast::Alternation is returned.
    pub fn into_ast(mut self) -> Ast {
        match self.asts.len() {
            0 => Ast::Empty(self.span),
            1 => self.asts.pop().unwrap(),
            _ => Ast::Alternation(self),
        }
    }
}

/// A concatenation of regular expressions.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AstConcat {
    /// The span of this concatenation.
    pub span: Span,
    /// The concatenation regular expressions.
    pub asts: Vec<Ast>,
}

impl AstConcat {
    /// Return this concatenation as an AST.
    ///
    /// If this concatenation contains zero ASTs, then Ast::Empty is
    /// returned. If this concatenation contains exactly 1 AST, then the
    /// corresponding AST is returned. Otherwise, Ast::Concat is returned.
    pub fn into_ast(mut self) -> Ast {
        match self.asts.len() {
            0 => Ast::Empty(self.span),
            1 => self.asts.pop().unwrap(),
            _ => Ast::Concat(self),
        }
    }
}

/// A single literal expression.
///
/// A literal corresponds to a single Unicode scalar value. Literals may be
/// represented in their literal form, e.g., `a` or in their escaped form,
/// e.g., `\x61`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AstLiteral {
    /// The span of this literal.
    pub span: Span,
    /// The kind of this literal.
    pub kind: AstLiteralKind,
    /// The Unicode scalar value corresponding to this literal.
    pub c: char,
}

/// The kind of a single literal expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AstLiteralKind {
    /// The literal is written verbatim, e.g., `a` or `☃`.
    Verbatim,
    /// The literal is written as a specially recognized escape, e.g., `\f`
    /// or `\n`.
    Special,
    /// The literal is written as an escape because it is punctuation, e.g.,
    /// `\*` or `\[`.
    Punctuation,
    /// The literal is written as an octal escape, e.g., `\141`.
    Octal,
    /// The literal is written as a two digit hex code, e.g., `\x61`.
    Hex,
    /// The literal is written as a Unicode escape, e.g., `\x{61}`.
    Unicode,
}

/// A single character class expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AstClass {
    /// A perl character class, e.g., `\d` or `\W`.
    Perl(AstClassPerl),
    /// An ASCII character class, e.g., `[[:alnum:]]` or `[[:punct:]]`.
    Ascii(AstClassAscii),
    /// A Unicode character class, e.g., `\pL` or `\p{Greek}`.
    Unicode(AstClassUnicode),
    /// A character class set, which may contain zero or more character ranges
    /// and/or zero or more nested classes. e.g., `[a-zA-Z\pL]`.
    Set(AstClassSet),
}

impl AstClass {
    /// Return the span of this character class.
    pub fn span(&self) -> &Span {
        match *self {
            AstClass::Perl(ref x) => &x.span,
            AstClass::Ascii(ref x) => &x.span,
            AstClass::Unicode(ref x) => &x.span,
            AstClass::Set(ref x) => &x.span,
        }
    }
}

/// A Perl character class.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AstClassPerl {
    /// The span of this class.
    pub span: Span,
    /// The kind of Perl class.
    pub kind: AstClassPerlKind,
    /// Whether the class is negated or not. e.g., `\d` is not negated but
    /// `\D` is.
    pub negated: bool,
}

/// The available Perl character classes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AstClassPerlKind {
    /// Decimal numbers.
    Digit,
    /// Whitespace.
    Space,
    /// Word characters.
    Word,
}

/// An ASCII character class.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AstClassAscii {
    /// The span of this class.
    pub span: Span,
    /// The kind of ASCII class.
    pub kind: AstClassAsciiKind,
    /// Whether the class is negated or not. e.g., `[[:alpha:]]` is not negated
    /// but `[[:^alpha:]]` is.
    pub negated: bool,
}

/// The available ASCII character classes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AstClassAsciiKind {
    /// `[0-9A-Za-z]`
    Alnum,
    /// `[A-Za-z]`
    Alpha,
    /// `[\x00-\x7F]`
    Ascii,
    /// `[ \t]`
    Blank,
    /// `[\x00-\x1F\x7F]`
    Cntrl,
    /// `[0-9]`
    Digit,
    /// `[!-~]`
    Graph,
    /// `[a-z]`
    Lower,
    /// `[ -~]`
    Print,
    /// `[!-/:-@\[-`{-~]`
    Punct,
    /// `[\t\n\v\f\r ]`
    Space,
    /// `[A-Z]`
    Upper,
    /// `[0-9A-Za-z_]`
    Word,
    /// `[0-9A-Fa-f]`
    Xdigit,
}

impl AstClassAsciiKind {
    /// Return the corresponding AstClassAsciiKind variant for the given name.
    ///
    /// The name given should correspond to the lowercase version of the
    /// variant name. e.g., `cntrl` is the name for `AstClassAsciiKind::Cntrl`.
    ///
    /// If no variant with the corresponding name exists, then `None` is
    /// returned.
    pub fn from_name(name: &str) -> Option<AstClassAsciiKind> {
        use self::AstClassAsciiKind::*;
        match name {
            "alnum" => Some(Alnum),
            "alpha" => Some(Alpha),
            "ascii" => Some(Ascii),
            "blank" => Some(Blank),
            "cntrl" => Some(Cntrl),
            "digit" => Some(Digit),
            "graph" => Some(Graph),
            "lower" => Some(Lower),
            "print" => Some(Print),
            "punct" => Some(Punct),
            "space" => Some(Space),
            "upper" => Some(Upper),
            "word" => Some(Word),
            "xdigit" => Some(Xdigit),
            _ => None,
        }
    }
}

/// A Unicode character class.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AstClassUnicode {
    /// The span of this class.
    pub span: Span,
    /// The kind of Unicode class.
    pub kind: AstClassUnicodeKind,
    /// Whether this class is negated or not.
    pub negated: bool,
    /// The name of the Unicode class. This corresponds to a Unicode
    /// general category or script.
    pub name: String,
}

/// The available forms of Unicode character classes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AstClassUnicodeKind {
    /// A one letter abbreviated class, e.g., `\pN`.
    OneLetter,
    /// A fully named class in braces, e.g., `\p{Greek}`.
    Bracketed,
}

/// A Unicode character class set, e.g., `[a-z0-9]`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AstClassSet {
    /// The span of this class.
    pub span: Span,
    /// Whether this class is negated or not. e.g., `[a]` is not negated but
    /// `[^a]` is.
    pub negated: bool,
    /// The top-level op of this set.
    pub op: AstClassSetOp,
}

/// An operation inside a character class set.
///
/// An operation is either a union of many things, or a binary operation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AstClassSetOp {
    /// A union of items in a class. A union may contain a single item.
    Union(AstClassSetUnion),
    /// A single binary operation (i.e., &&, -- or ~~).
    BinaryOp(AstClassSetBinaryOp),
}

impl AstClassSetOp {
    /// Return the span of this character class set operation.
    pub fn span(&self) -> &Span {
        match *self {
            AstClassSetOp::Union(ref x) => &x.span,
            AstClassSetOp::BinaryOp(ref x) => &x.span,
        }
    }
}

/// A union of items inside a character class set.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AstClassSetUnion {
    /// The span of the items in this operation. e.g., the `a-z0-9` in
    /// `[^a-z0-9]`
    pub span: Span,
    /// The sequence of items that make up this union.
    pub items: Vec<AstClassSetItem>,
}

impl AstClassSetUnion {
    /// Push a new item in this union.
    ///
    /// The ending position of this union's span is updated to the ending
    /// position of the span of the item given. If the union is empty, then
    /// the starting position of this union is set to the starting position
    /// of this item.
    ///
    /// In other words, if you only use this method to add items to a union
    /// and you set the spans on each item correctly, then you should never
    /// need to adjust the span of the union directly.
    pub fn push(&mut self, item: AstClassSetItem) {
        if self.items.is_empty() {
            self.span.start = item.span().start;
        }
        self.span.end = item.span().end;
        self.items.push(item);
    }
}

/// A single component of a character class set.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AstClassSetItem {
    /// A single literal.
    Literal(AstLiteral),
    /// A range between two literals.
    Range(AstClassSetRange),
    /// A nested character class.
    Class(Box<AstClass>),
}

impl AstClassSetItem {
    /// Return the span of this character class set item.
    pub fn span(&self) -> &Span {
        match *self {
            AstClassSetItem::Literal(ref x) => &x.span,
            AstClassSetItem::Range(ref x) => &x.span,
            AstClassSetItem::Class(ref x) => x.span(),
        }
    }
}

/// A single character class range in a set.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AstClassSetRange {
    /// The span of this range.
    pub span: Span,
    /// The start of this range.
    pub start: AstLiteral,
    /// The end of this range.
    pub end: AstLiteral,
}

/// A Unicode character class set operation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AstClassSetBinaryOp {
    /// The span of this operation. e.g., the `a-z--[h-p]` in `[a-z--h-p]`.
    pub span: Span,
    /// The type of this set operation.
    pub kind: AstClassSetBinaryOpKind,
    /// The left hand side of the operation.
    pub lhs: Box<AstClassSetOp>,
    /// The right hand side of the operation.
    pub rhs: Box<AstClassSetOp>,
}

/// The type of a Unicode character class set operation.
///
/// Note that this doesn't explicitly represent union since there is no
/// explicit union operator. Concatenation inside a character class corresponds
/// to the union operation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AstClassSetBinaryOpKind {
    /// The intersection of two sets, e.g., `\pN&&[a-z]`.
    Intersection,
    /// The difference of two sets, e.g., `\pN--[0-9]`.
    Difference,
    /// The symmetric difference of two sets. The symmetric difference is the
    /// set of elements belonging to one but not both sets.
    /// e.g., `[\pL~~[:ascii:]]`.
    SymmetricDifference,
}

/// A single zero-width assertion.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AstAssertion {
    /// The span of this assertion.
    pub span: Span,
    /// The assertion kind, e.g., `\b` or `^`.
    pub kind: AstAssertionKind,
}

/// An assertion kind.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AstAssertionKind {
    /// `^`
    StartLine,
    /// `$`
    EndLine,
    /// `\A`
    StartText,
    /// `\z`
    EndText,
    /// `\b`
    WordBoundary,
    /// `\B`
    NotWordBoundary,
}

/// A repetition operation applied to a regular expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AstRepetition {
    /// The span of this operation.
    pub span: Span,
    /// The actual operation.
    pub op: AstRepetitionOp,
    /// Whether this operation was applied greedily or not.
    pub greedy: bool,
    /// The regular expression under repetition.
    pub ast: Box<Ast>,
}

/// The repetition operator itself.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AstRepetitionOp {
    /// The span of this operator. This includes things like `+`, `*?` and
    /// `{m,n}`.
    pub span: Span,
    /// The type of operation.
    pub kind: AstRepetitionKind,
}

/// The kind of a repetition operator.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AstRepetitionKind {
    /// `?`
    ZeroOrOne,
    /// `*`
    ZeroOrMore,
    /// `+`
    OneOrMore,
    /// `{m,n}`
    Range(AstRepetitionRange),
}

/// A range repetition operator.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AstRepetitionRange {
    /// `{m}`
    Exactly(u32),
    /// `{m,}`
    AtLeast(u32),
    /// `{m,n}`
    Bounded(u32, u32),
}

/// A grouped regular expression.
///
/// This includes both capturing and non-capturing groups. This does **not**
/// include flag-only groups like `(?is)`, but does contain any group that
/// contains a sub-expression, e.g., `(a)`, `(?P<name>a)`, `(?:a)` and
/// `(?is:a)`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AstGroup {
    /// The span of this group.
    pub span: Span,
    /// The kind of this group.
    pub kind: AstGroupKind,
    /// The regular expression in this group.
    pub ast: Box<Ast>,
}

impl AstGroup {
    /// If this group is non-capturing, then this returns the (possibly empty)
    /// set of flags. Otherwise, `None` is returned.
    pub fn flags(&self) -> Option<&AstFlags> {
        match self.kind {
            AstGroupKind::NonCapturing(ref flags) => Some(flags),
            _ => None,
        }
    }
}

/// The kind of a group.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AstGroupKind {
    /// `(a)`
    CaptureIndex,
    /// `(?P<name>a)`
    CaptureName(AstCaptureName),
    /// `(?:a)` and `(?i:a)`
    NonCapturing(AstFlags),
}

/// A capture name.
///
/// This corresponds to the name itself between the angle brackets in, e.g.,
/// `(?P<foo>expr)`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AstCaptureName {
    /// The span of this capture name.
    pub span: Span,
    /// The capture name.
    pub name: String,
}

/// A group of flags that is not applied to a particular regular expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AstSetFlags {
    /// The span of these flags, including the grouping parentheses.
    pub span: Span,
    /// The actual sequence of flags.
    pub flags: AstFlags,
}

/// A group of flags.
///
/// This corresponds only to the sequence of flags themselves, e.g., `is-u`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AstFlags {
    /// The span of this group of flags.
    pub span: Span,
    /// A sequence of flag items. Each item is either a flag or a negation
    /// operator.
    pub items: Vec<AstFlagsItem>,
}

impl AstFlags {
    /// Add the given item to this sequence of flags.
    ///
    /// If the item was added successfully, then `None` is returned. If the
    /// given item is a duplicate, then `Some(i)` is returned, where
    /// `items[i].kind == item.kind`.
    pub fn add_item(&mut self, item: AstFlagsItem) -> Option<usize> {
        for (i, x) in self.items.iter().enumerate() {
            if x.kind == item.kind {
                return Some(i);
            }
        }
        self.items.push(item);
        None
    }

    /// Returns the state of the given flag in this set.
    ///
    /// If the given flag is in the set but is negated, then `Some(false)` is
    /// returned.
    ///
    /// If the given flag is in the set and is not negated, then `Some(true)`
    /// is returned.
    ///
    /// Otherwise, `None` is returned.
    pub fn flag_state(&self, flag: AstFlag) -> Option<bool> {
        let mut negated = false;
        for x in &self.items {
            match x.kind {
                AstFlagsItemKind::Negation => {
                    negated = true;
                }
                AstFlagsItemKind::Flag(ref xflag) if xflag == &flag => {
                    return Some(!negated);
                }
                _ => {}
            }
        }
        None
    }
}

/// A single item in a group of flags.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AstFlagsItem {
    /// The span of this item.
    pub span: Span,
    /// The kind of this item.
    pub kind: AstFlagsItemKind,
}

/// The kind of an item in a group of flags.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AstFlagsItemKind {
    /// A negation operator applied to all subsequent flags in the enclosing
    /// group.
    Negation,
    /// A single flag in a group.
    Flag(AstFlag),
}

impl AstFlagsItemKind {
    /// Returns true if and only if this item is a negation operator.
    pub fn is_negation(&self) -> bool {
        match *self {
            AstFlagsItemKind::Negation => true,
            _ => false,
        }
    }
}

/// A single flag.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AstFlag {
    /// `i`
    CaseInsensitive,
    /// `m`
    MultiLine,
    /// `s`
    DotMatchesNewLine,
    /// `U`
    SwapGreed,
    /// `u`
    Unicode,
    /// `x`
    IgnoreWhitespace,
}

impl fmt::Display for AstFlag {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::AstFlag::*;
        match *self {
            CaseInsensitive => write!(f, "i"),
            MultiLine => write!(f, "m"),
            DotMatchesNewLine => write!(f, "s"),
            SwapGreed => write!(f, "U"),
            Unicode => write!(f, "u"),
            IgnoreWhitespace => write!(f, "x"),
        }
    }
}

/// Returns an error if the given AST exceeds the given depth limit.
pub fn error_if_nested(
    ast: &Ast,
    limit: u32,
    depth: u32,
) -> Result<(), AstError> {
    if depth >= limit {
        return Err(AstError {
            span: *ast.span(),
            kind: AstErrorKind::NestLimitExceeded(limit),
        });
    }
    match *ast {
        Ast::Empty(_)
        | Ast::Flags(_)
        | Ast::Literal(_)
        | Ast::Dot(_)
        | Ast::Assertion(_) => {
            Ok(())
        }
        Ast::Class(ref cls) => {
            error_if_nested_class(cls, limit, depth)
        }
        Ast::Repetition(AstRepetition { ref ast, .. }) => {
            error_if_nested(ast, limit, depth.checked_add(1).unwrap())
        }
        Ast::Group(AstGroup { ref ast, .. }) => {
            error_if_nested(ast, limit, depth.checked_add(1).unwrap())
        }
        Ast::Alternation(AstAlternation { ref asts, .. }) => {
            let depth = depth.checked_add(1).unwrap();
            for ast in asts {
                try!(error_if_nested(ast, limit, depth));
            }
            Ok(())
        }
        Ast::Concat(AstConcat { ref asts, .. }) => {
            let depth = depth.checked_add(1).unwrap();
            for ast in asts {
                try!(error_if_nested(ast, limit, depth));
            }
            Ok(())
        }
    }
}

/// Returns an error if the given AST class exceeds the given depth limit.
fn error_if_nested_class(
    class: &AstClass,
    limit: u32,
    depth: u32,
) -> Result<(), AstError> {
    if depth >= limit {
        return Err(AstError {
            span: *class.span(),
            kind: AstErrorKind::NestLimitExceeded(limit),
        });
    }
    match *class {
        AstClass::Perl(_)
        | AstClass::Ascii(_)
        | AstClass::Unicode(_) => Ok(()),
        AstClass::Set(AstClassSet { ref op, .. }) => {
            error_if_nested_class_op(op, limit, depth)
        }
    }
}

fn error_if_nested_class_op(
    op: &AstClassSetOp,
    limit: u32,
    depth: u32,
) -> Result<(), AstError> {
    if depth >= limit {
        return Err(AstError {
            span: *op.span(),
            kind: AstErrorKind::NestLimitExceeded(limit),
        });
    }
    match *op {
        AstClassSetOp::Union(AstClassSetUnion { ref items, .. }) => {
            for item in items {
                match *item {
                    AstClassSetItem::Literal(_)
                    | AstClassSetItem::Range(_) => {}
                    AstClassSetItem::Class(ref cls) => {
                        let depth = depth.checked_add(1).unwrap();
                        try!(error_if_nested_class(cls, limit, depth));
                    }
                }
            }
            Ok(())
        }
        AstClassSetOp::BinaryOp(AstClassSetBinaryOp {
            ref lhs, ref rhs, ..
        }) => {
            let depth = depth.checked_add(1).unwrap();
            try!(error_if_nested_class_op(lhs, limit, depth));
            try!(error_if_nested_class_op(rhs, limit, depth));
            Ok(())
        }
    }
}
