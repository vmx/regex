// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![allow(dead_code)]
// #![deny(missing_docs)]

/*!
TODO.
*/

/// Span represents the position information of a single AST item.
///
/// All span positions are absolute byte offsets that can be used on the
/// original regular expression that was parsed.
pub struct Span {
    /// The start byte offset.
    pub start: usize,
    /// The end byte offset.
    pub end: usize,
}

/// A comment from a regular expression with an associated span.
///
/// A regular expression can only contain comments when the `x` flag is
/// enabled.
pub struct Comment {
    /// The span of this comment, including the beginning `#`.
    pub span: Span,
    /// The comment text, starting with the first character following the `#`.
    pub comment: String,
}

/// An abstract syntax tree for a singular expression along with comments
/// found.
///
/// Comments are not stored in the tree itself to avoid complexity. Each
/// comment contains a span of precisely where it occurred in the original
/// regular expression.
pub struct AstWithComments {
    /// The actual ast.
    pub ast: Ast,
    /// All comments found in the original regular expression.
    pub comments: Vec<Comment>,
}

/// An abstract syntax tree for a single regular expression.
pub enum Ast {
    /// An empty regex that matches exactly the empty string.
    EmptyString(Span),
    /// A single character literal, which includes escape sequences.
    Literal(AstLiteral),
    /// A single character class. This includes all forms of character classes,
    /// e.g., `\d`, `\pN`, `[a-z]` and `[[:alpha:]]`.
    Class(AstClass),
    /// A single zero-width assertion.
    Assertion(AstAssertion),
    /// A repetition operator applied to an arbitrary regular expression.
    Repetition(AstRepetition),
    /// A grouped regular expression.
    Group(AstGroup),
    /// A set of flags, e.g., `(?is)`.
    Flags(AstSetFlags),
    /// An alternation of regular expressions.
    Alternation(AstAlternation),
    /// A concatenation of regular expressions.
    Concat(AstConcat),
}

impl Ast {
    /// Return the span of this abstract syntax tree.
    pub fn span(&self) -> &Span {
        match *self {
            Ast::EmptyString(ref span) => span,
            Ast::Literal(ref x) => &x.span,
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
pub struct AstAlternation {
    /// The span of this alternation.
    pub span: Span,
    /// The alternate regular expressions.
    pub asts: Vec<Ast>,
}

/// A concatenation of regular expressions.
pub struct AstConcat {
    /// The span of this concatenation.
    pub span: Span,
    /// The concatenation regular expressions.
    pub asts: Vec<Ast>,
}

/// A single literal expression.
///
/// A literal corresponds to a single Unicode scalar value. Literals may be
/// represented in their literal form, e.g., `a` or in their escaped form,
/// e.g., `\x61`.
pub struct AstLiteral {
    /// The span of this literal.
    pub span: Span,
    /// The kind of this literal.
    pub kind: AstLiteralKind,
    /// The Unicode scalar value corresponding to this literal.
    pub c: char,
}

/// The kind of a single literal expression.
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
pub enum AstClass {
    /// The special "any character" class, i.e., `.`.
    Dot(Span),
    /// A perl character class, e.g., `\d` or `\W`.
    Perl(AstClassPerl),
    /// An ASCII character class, e.g., `[[:alnum:]]` or `[[:punct:]]`.
    Ascii(AstClassAscii),
    /// A Unicode character class, e.g., `\pL` or `\p{Greek}`.
    Unicode(AstClassUnicode),
    /// A character class set, which may contain zero or more character ranges
    /// and/or zero or more nested classes. e.g., `[a-zA-Z]`.
    Set(AstClassSet),
}

impl AstClass {
    /// Return the span of this character class.
    pub fn span(&self) -> &Span {
        match *self {
            AstClass::Dot(ref span) => span,
            AstClass::Perl(ref x) => &x.span,
            AstClass::Ascii(ref x) => &x.span,
            AstClass::Unicode(ref x) => &x.span,
            AstClass::Set(ref x) => &x.span,
        }
    }
}

/// A Perl character class.
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
pub enum AstClassPerlKind {
    /// Decimal numbers.
    Digit,
    /// Whitespace.
    Space,
    /// Word characters.
    Word,
}

/// An ASCII character class.
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

/// A Unicode character class.
pub struct AstClassUnicode {
    /// The span of this class.
    pub span: Span,
    /// The kind of Unicode class.
    pub kind: AstClassUnicodeKind,
    /// The name of the Unicode class. This corresponds to a Unicode
    /// general category or script.
    pub name: String,
}

/// The available forms of Unicode character classes.
pub enum AstClassUnicodeKind {
    /// A one letter abbreviated class, e.g., `\pN`.
    OneLetter,
    /// A fully named class, e.g., `\p{Greek}`.
    FullName,
}

/// A Unicode character class set, e.g., `[a-z0-9]`.
pub struct AstClassSet {
    /// The span of this class.
    pub span: Span,
    /// Whether this class is negated or not. e.g., `[a]` is not negated but
    /// `[^a]` is.
    pub negated: bool,
    /// The sequence of items that make up this set.
    pub items: Vec<AstClassSetItem>,
}

/// A single component of a character class set.
pub enum AstClassSetItem {
    /// A single literal.
    Literal(AstLiteral),
    /// A range between two literals.
    Range(AstClassSetRange),
    /// A nested character class.
    Class(Box<AstClass>),
    /// A Unicode character class set operation. e.g., `[\pL--a]`.
    Op(AstClassSetOp),
}

impl AstClassSetItem {
    /// Return the span of this character class set item.
    pub fn span(&self) -> &Span {
        match *self {
            AstClassSetItem::Literal(ref x) => &x.span,
            AstClassSetItem::Range(ref x) => &x.span,
            AstClassSetItem::Class(ref x) => x.span(),
            AstClassSetItem::Op(ref x) => &x.span,
        }
    }
}

/// A single character class range in a set.
pub struct AstClassSetRange {
    /// The span of this range.
    pub span: Span,
    /// The start of this range.
    pub start: AstLiteral,
    /// The end of this range.
    pub end: AstLiteral,
}

/// A Unicode character class set operation.
pub struct AstClassSetOp {
    /// The span of this operation.
    pub span: Span,
    /// The type of this set operation.
    pub kind: AstClassSetOpKind,
    /// The left hand side of the operation.
    pub class1: Box<AstClass>,
    /// The right hand side of the operation.
    pub class2: Box<AstClass>,
}

/// The type of a Unicode character class set operation.
///
/// Note that this doesn't explicitly represent union since there is no
/// explicit union operator. Concatenation inside a character class corresponds
/// to the union operation.
pub enum AstClassSetOpKind {
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
pub struct AstAssertion {
    /// The span of this assertion.
    pub span: Span,
    /// The assertion kind, e.g., `\b` or `^`.
    pub kind: AstAssertionKind,
}

/// An assertion kind.
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
pub struct AstRepetition {
    /// The span of this operation.
    pub span: Span,
    /// The actual operation.
    pub kind: AstRepetitionKind,
    /// Whether this operation was applied greedily or not.
    pub greedy: bool,
    /// The regular expression under repetition.
    pub ast: Box<Ast>,
}

/// The kind of a repetition operator.
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
pub struct AstGroup {
    /// The span of this group.
    pub span: Span,
    /// The kind of this group.
    pub kind: AstGroupKind,
    /// The regular expression in this group.
    pub ast: Box<Ast>,
}

/// The kind of a group.
pub enum AstGroupKind {
    /// `(a)`
    CaptureIndex,
    /// `(?P<name>a)`
    CaptureName(String),
    /// `(?:a)` and `(?i:a)`
    NonCapturing(AstFlags),
}

/// A group of flags that is not applied to a particular regular expression.
pub struct AstSetFlags {
    /// The span of these flags, including the grouping parentheses.
    pub span: Span,
    /// The actual sequence of flags.
    pub flags: AstFlags,
}

/// A group of flags.
///
/// This corresponds only to the sequence of flags themselves, e.g., `is-u`.
pub struct AstFlags {
    /// The span of this group of flags.
    pub span: Span,
    /// A sequence of flag items. Each item is either a flag or a negation
    /// operator.
    pub items: Vec<AstFlagsItem>,
}

/// A single item in a group of flags.
pub struct AstFlagsItem {
    /// The span of this item.
    pub span: Span,
    /// The kind of this item.
    pub kind: AstFlagsItemKind,
}

/// The kind of an item in a group of flags.
pub enum AstFlagsItemKind {
    /// A negation operator applied to all subsequent flags in the enclosing
    /// group.
    Negation,
    /// A single flag in a group.
    Flag(AstFlag),
}

/// A single flag.
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
