use std::cell::Cell;
use std::result;

use ast::*;

type Result<T> = result::Result<T, AstError>;

/// A regular expression parser.
///
/// This parses a string representation of a regular expression into an
/// abstract syntax tree.
pub struct Parser<'s> {
    /// The full regular expression provided by the user.
    s: &'s str,
    /// The current position of the parser.
    index: Cell<usize>,
}

impl<'s> Parser<'s> {
    /// Return the current position of the parser.
    fn pos(&self) -> usize {
        self.index.get()
    }

    /// Return the character at the current position of the parser.
    ///
    /// This panics if the current position does not point to a valid char.
    fn char(&self) -> char {
        self.char_at(self.pos())
    }

    /// Return the character at the given position.
    ///
    /// This panics if the given position does not point to a valid char.
    fn char_at(&self, i: usize) -> char {
        self.s[i..].chars().next().unwrap()
    }

    /// Bump the parser to the next Unicode scalar value.
    ///
    /// If the end of the input has been reached, then `false` is returned.
    fn bump(&self) -> bool {
        self.index.set(self.pos() + self.char().len_utf8());
        self.s[self.index.get()..].chars().next().is_some()
    }

    /// Peek at the next character in the input without advancing the parser.
    ///
    /// If the input has been exhausted, then this returns `None`.
    fn peek(&self) -> Option<char> {
        self.s[self.pos() + self.char().len_utf8()..].chars().next()
    }
}

impl<'s> Parser<'s> {
    fn parse_flag(&self) -> Result<AstFlag> {
        match self.char() {
            'i' => Ok(AstFlag::CaseInsensitive),
            'm' => Ok(AstFlag::MultiLine),
            's' => Ok(AstFlag::DotMatchesNewLine),
            'U' => Ok(AstFlag::SwapGreed),
            'u' => Ok(AstFlag::Unicode),
            'x' => Ok(AstFlag::IgnoreWhitespace),
            c => Err(AstError {
                span: Span {
                    start: self.pos(),
                    end: self.pos() + c.len_utf8(),
                },
                kind: AstErrorKind::UnrecognizedFlag(c),
            }),
        }
    }
}
