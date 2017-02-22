use std::cell::{Cell, RefCell};
use std::result;

use ast::*;

type Result<T> = result::Result<T, AstError>;

#[derive(Debug)]
enum Either<Left, Right> {
    Left(Left),
    Right(Right),
}

/// A regular expression parser.
///
/// This parses a string representation of a regular expression into an
/// abstract syntax tree.
pub struct Parser<'p> {
    /// The full regular expression provided by the user.
    pattern: &'p str,
    /// The current position of the parser.
    index: Cell<usize>,
    /// A stack of sub-expressions.
    stack: RefCell<Vec<Ast>>,
}

impl<'p> Parser<'p> {
    /// Create a new parser for the given regular expression.
    pub fn new(pattern: &str) -> Parser {
        Parser {
            pattern: pattern,
            index: Cell::new(0),
            stack: RefCell::new(vec![]),
        }
    }

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
        self.pattern[i..].chars().next().unwrap()
    }

    /// Bump the parser to the next Unicode scalar value.
    ///
    /// If the end of the input has been reached, then `false` is returned.
    fn bump(&self) -> bool {
        self.index.set(self.pos() + self.char().len_utf8());
        self.pattern[self.index.get()..].chars().next().is_some()
    }

    /// If the substring starting at the current position of the parser has
    /// the given prefix, then bump the parser to the character immediately
    /// following the prefix and return true. Otherwise, don't bump the parser
    /// and return false.
    fn bump_if(&self, prefix: &str) -> bool {
        if self.pattern[self.pos()..].starts_with(prefix) {
            self.index.set(self.pos() + prefix.len());
            true
        } else {
            false
        }
    }

    /// Peek at the next character in the input without advancing the parser.
    ///
    /// If the input has been exhausted, then this returns `None`.
    fn peek(&self) -> Option<char> {
        self.pattern[self.pos() + self.char().len_utf8()..].chars().next()
    }

    /// Returns true if the next call to `bump` would return false.
    fn is_eof(&self) -> bool {
        self.pattern[self.pos()..].chars().next().is_none()
    }

    /// Create a span at the current position of the parser. Both the start
    /// and end of the span are set.
    fn span(&self) -> Span {
        Span::new(self.pos()..self.pos())
    }

    /// Create a span that covers the current character.
    fn span_char(&self) -> Span {
        Span::new(self.pos()..self.pos() + self.char().len_utf8())
    }

    /// Push an AST on to the parser's internal stack.
    fn push(&self, x: Ast) {
        self.stack.borrow_mut().push(x);
    }

    /// Pop an AST from the parser's internal stack.
    ///
    /// If the stack is empty, then `None` is returned.
    fn pop(&self) -> Option<Ast> {
        self.stack.borrow_mut().pop()
    }

    /// Pop a group AST from the parser's internal stack.
    ///
    /// If the group contains an alternation, then return that as well.
    ///
    /// If no such group could be popped, then an unopened group error is
    /// returned.
    fn pop_group(&self) -> Result<(AstGroup, Option<AstAlternation>)> {
        match self.pop() {
            Some(Ast::Group(group)) => return Ok((group, None)),
            Some(Ast::Alternation(alt)) => {
                match self.pop() {
                    Some(Ast::Group(group)) => {
                        return Ok((group, Some(alt)));
                    }
                    _ => {}
                }
            }
            _ => {}
        }
        Err(AstError {
            span: self.span_char(),
            kind: AstErrorKind::GroupUnopened,
        })
    }
}

impl<'s> Parser<'s> {
    /// Parse the regular expression.
    fn parse(&self) -> Result<Ast> {
        if self.is_eof() {
            return Ok(Ast::EmptyString(self.span()));
        }
        Ok(try!(self.parse_concat()).into_ast())
    }

    fn parse_concat(&self) -> Result<AstConcat> {
        let mut concat = AstConcat {
            span: self.span(),
            asts: vec![],
        };
        loop {
            match self.char() {
                '(' => {
                    let sub_span = self.span();
                    match try!(self.parse_group()) {
                        Either::Left(set) => {
                            concat.asts.push(Ast::Flags(set));
                        }
                        Either::Right(group) => {
                            self.push(Ast::Concat(concat));
                            self.push(Ast::Group(group));
                            concat = AstConcat {
                                span: sub_span,
                                asts: vec![],
                            };
                        }
                    }
                }
                ')' => {
                    let (mut group, alt) = try!(self.pop_group());
                    concat.span.end = self.pos();
                    group.span.end = self.span_char().end;
                    if concat.asts.is_empty() {
                        return Err(AstError {
                            span: group.span,
                            kind: AstErrorKind::GroupEmpty,
                        });
                    }

                    if let Some(mut alt) = alt {
                        alt.asts.push(Ast::Concat(concat));
                        group.ast = Box::new(Ast::Alternation(alt));
                    } else {
                        group.ast = Box::new(Ast::Concat(concat));
                    }
                    match self.pop() {
                        Some(Ast::Concat(up_concat)) => {
                            concat = up_concat;
                        }
                        _ => unreachable!(),
                    }
                }
                _ => unreachable!(),
            }
            if !self.bump() {
                break;
            }
        }
        concat.span.end = self.pos();
        Ok(concat)
    }

    /// Parse a group (which contains a sub-expression) or a set of flags.
    ///
    /// If a group was found, then it is returned with an empty AST. If a set
    /// of flags is found, then that set is returned.
    ///
    /// The parser should be positioned at the opening parenthesis.
    ///
    /// This advances the parser to the character before the start of the
    /// sub-expression (in the case of a group) or to the closing parenthesis
    /// immediately following the set of flags.
    ///
    /// # Errors
    ///
    /// If flags are given and incorrectly specified, then a corresponding
    /// error is returned.
    ///
    /// If a capture name is given and it is incorrectly specified, then a
    /// corresponding error is returned.
    fn parse_group(&self) -> Result<Either<AstSetFlags, AstGroup>> {
        let open_span = self.span_char();
        if self.bump_if("(?P<") {
            let cap = try!(self.parse_capture_name());
            Ok(Either::Right(AstGroup {
                span: open_span,
                kind: AstGroupKind::CaptureName(cap),
                ast: Box::new(Ast::EmptyString(self.span())),
            }))
        } else if self.bump_if("(?") {
            let flags = try!(self.parse_flags());
            match self.char() {
                ')' => {
                    Ok(Either::Left(AstSetFlags {
                        span: Span { end: self.span_char().end, ..open_span },
                        flags: flags,
                    }))
                }
                ':' => {
                    Ok(Either::Right(AstGroup {
                        span: open_span,
                        kind: AstGroupKind::NonCapturing(flags),
                        ast: Box::new(Ast::EmptyString(self.span())),
                    }))
                }
                _ => unreachable!()
            }
        } else {
            Ok(Either::Right(AstGroup {
                span: open_span,
                kind: AstGroupKind::CaptureIndex,
                ast: Box::new(Ast::EmptyString(self.span())),
            }))
        }
    }

    fn parse_capture_name(&self) -> Result<AstCaptureName> {
        unimplemented!()
    }

    /// Parse a sequence of flags starting at the current character.
    ///
    /// This advances the parser to the character immediately following the
    /// final flag in the set.
    ///
    /// # Errors
    ///
    /// If any flags are duplicated, then an error is returned.
    ///
    /// If the negation operator is used more than once, then an error is
    /// returned.
    ///
    /// If no flags could be found or if the negation operation is not followed
    /// by any flags, then an error is returned.
    fn parse_flags(&self) -> Result<AstFlags> {
        let mut flags = AstFlags {
            span: self.span(),
            items: vec![],
        };
        while self.char() != ':' && self.char() != ')' {
            if self.char() == '-' {
                let item = AstFlagsItem {
                    span: self.span_char(),
                    kind: AstFlagsItemKind::Negation,
                };
                if let Some(i) = flags.add_item(item) {
                    return Err(AstError {
                        span: self.span_char(),
                        kind: AstErrorKind::FlagRepeatedNegation {
                            original: flags.items[i].span,
                        },
                    });
                }
            } else {
                let item = AstFlagsItem {
                    span: self.span_char(),
                    kind: AstFlagsItemKind::Flag(try!(self.parse_flag())),
                };
                if let Some(i) = flags.add_item(item) {
                    return Err(AstError {
                        span: self.span_char(),
                        kind: AstErrorKind::FlagDuplicate {
                            flag: self.char(),
                            original: flags.items[i].span,
                        },
                    });
                }
            }
            if !self.bump() {
                return Err(AstError {
                    span: self.span(),
                    kind: AstErrorKind::FlagUnexpectedEof,
                });
            }
        }
        flags.span.end = self.pos();
        return Ok(flags);
    }

    /// Parse the current character as a flag.
    ///
    /// This does not advance the parser.
    ///
    /// # Errors
    ///
    /// If the flag is not recognized, then an error is returned.
    fn parse_flag(&self) -> Result<AstFlag> {
        match self.char() {
            'i' => Ok(AstFlag::CaseInsensitive),
            'm' => Ok(AstFlag::MultiLine),
            's' => Ok(AstFlag::DotMatchesNewLine),
            'U' => Ok(AstFlag::SwapGreed),
            'u' => Ok(AstFlag::Unicode),
            'x' => Ok(AstFlag::IgnoreWhitespace),
            c => Err(AstError {
                span: self.span_char(),
                kind: AstErrorKind::FlagUnrecognized { flag: c },
            }),
        }
    }
}

#[cfg(test)]
mod tests {
    use ast::*;
    use super::Parser;

    fn parser(pattern: &str) -> Parser {
        Parser::new(pattern)
    }

    #[test]
    fn parse_group() {
        assert_eq!(parser("(?i)").parse(), Ok(Ast::Flags(AstSetFlags {
            span: Span::new(0..4),
            flags: AstFlags {
                span: Span::new(2..3),
                items: vec![AstFlagsItem {
                    span: Span::new(2..3),
                    kind: AstFlagsItemKind::Flag(AstFlag::CaseInsensitive),
                }],
            },
        })));
        assert_eq!(parser("(?iU)").parse(), Ok(Ast::Flags(AstSetFlags {
            span: Span::new(0..5),
            flags: AstFlags {
                span: Span::new(2..4),
                items: vec![
                    AstFlagsItem {
                        span: Span::new(2..3),
                        kind: AstFlagsItemKind::Flag(AstFlag::CaseInsensitive),
                    },
                    AstFlagsItem {
                        span: Span::new(3..4),
                        kind: AstFlagsItemKind::Flag(AstFlag::SwapGreed),
                    },
                ],
            },
        })));
        assert_eq!(parser("(?i-U)").parse(), Ok(Ast::Flags(AstSetFlags {
            span: Span::new(0..6),
            flags: AstFlags {
                span: Span::new(2..5),
                items: vec![
                    AstFlagsItem {
                        span: Span::new(2..3),
                        kind: AstFlagsItemKind::Flag(AstFlag::CaseInsensitive),
                    },
                    AstFlagsItem {
                        span: Span::new(3..4),
                        kind: AstFlagsItemKind::Negation,
                    },
                    AstFlagsItem {
                        span: Span::new(4..5),
                        kind: AstFlagsItemKind::Flag(AstFlag::SwapGreed),
                    },
                ],
            },
        })));

        assert_eq!(parser(")").parse(), Err(AstError {
            span: Span::new(0..1),
            kind: AstErrorKind::GroupUnopened,
        }));
        assert_eq!(parser("()").parse(), Err(AstError {
            span: Span::new(0..2),
            kind: AstErrorKind::GroupEmpty,
        }));
    }

    #[test]
    fn parse_flags() {
        assert_eq!(parser("i:").parse_flags(), Ok(AstFlags {
            span: Span::new(0..1),
            items: vec![AstFlagsItem {
                span: Span::new(0..1),
                kind: AstFlagsItemKind::Flag(AstFlag::CaseInsensitive),
            }],
        }));
        assert_eq!(parser("i)").parse_flags(), Ok(AstFlags {
            span: Span::new(0..1),
            items: vec![AstFlagsItem {
                span: Span::new(0..1),
                kind: AstFlagsItemKind::Flag(AstFlag::CaseInsensitive),
            }],
        }));

        assert_eq!(parser("isU:").parse_flags(), Ok(AstFlags {
            span: Span::new(0..3),
            items: vec![
                AstFlagsItem {
                    span: Span::new(0..1),
                    kind: AstFlagsItemKind::Flag(AstFlag::CaseInsensitive),
                },
                AstFlagsItem {
                    span: Span::new(1..2),
                    kind: AstFlagsItemKind::Flag(AstFlag::DotMatchesNewLine),
                },
                AstFlagsItem {
                    span: Span::new(2..3),
                    kind: AstFlagsItemKind::Flag(AstFlag::SwapGreed),
                },
            ],
        }));

        assert_eq!(parser("-isU:").parse_flags(), Ok(AstFlags {
            span: Span::new(0..4),
            items: vec![
                AstFlagsItem {
                    span: Span::new(0..1),
                    kind: AstFlagsItemKind::Negation,
                },
                AstFlagsItem {
                    span: Span::new(1..2),
                    kind: AstFlagsItemKind::Flag(AstFlag::CaseInsensitive),
                },
                AstFlagsItem {
                    span: Span::new(2..3),
                    kind: AstFlagsItemKind::Flag(AstFlag::DotMatchesNewLine),
                },
                AstFlagsItem {
                    span: Span::new(3..4),
                    kind: AstFlagsItemKind::Flag(AstFlag::SwapGreed),
                },
            ],
        }));
        assert_eq!(parser("i-sU:").parse_flags(), Ok(AstFlags {
            span: Span::new(0..4),
            items: vec![
                AstFlagsItem {
                    span: Span::new(0..1),
                    kind: AstFlagsItemKind::Flag(AstFlag::CaseInsensitive),
                },
                AstFlagsItem {
                    span: Span::new(1..2),
                    kind: AstFlagsItemKind::Negation,
                },
                AstFlagsItem {
                    span: Span::new(2..3),
                    kind: AstFlagsItemKind::Flag(AstFlag::DotMatchesNewLine),
                },
                AstFlagsItem {
                    span: Span::new(3..4),
                    kind: AstFlagsItemKind::Flag(AstFlag::SwapGreed),
                },
            ],
        }));

        assert_eq!(parser("isU").parse_flags(), Err(AstError {
            span: Span::new(3..3),
            kind: AstErrorKind::FlagUnexpectedEof,
        }));
        assert_eq!(parser("isUa:").parse_flags(), Err(AstError {
            span: Span::new(3..4),
            kind: AstErrorKind::FlagUnrecognized { flag: 'a' },
        }));
        assert_eq!(parser("isUi:").parse_flags(), Err(AstError {
            span: Span::new(3..4),
            kind: AstErrorKind::FlagDuplicate {
                flag: 'i',
                original: Span::new(0..1),
            },
        }));
        assert_eq!(parser("i-sU-i:").parse_flags(), Err(AstError {
            span: Span::new(4..5),
            kind: AstErrorKind::FlagRepeatedNegation {
                original: Span::new(1..2),
            },
        }));
    }

    #[test]
    fn parse_flag() {
        assert_eq!(parser("i").parse_flag(), Ok(AstFlag::CaseInsensitive));
        assert_eq!(parser("m").parse_flag(), Ok(AstFlag::MultiLine));
        assert_eq!(parser("s").parse_flag(), Ok(AstFlag::DotMatchesNewLine));
        assert_eq!(parser("U").parse_flag(), Ok(AstFlag::SwapGreed));
        assert_eq!(parser("u").parse_flag(), Ok(AstFlag::Unicode));
        assert_eq!(parser("x").parse_flag(), Ok(AstFlag::IgnoreWhitespace));

        assert_eq!(parser("a").parse_flag(), Err(AstError {
            span: Span::new(0..1),
            kind: AstErrorKind::FlagUnrecognized { flag: 'a' },
        }));
        assert_eq!(parser("☃").parse_flag(), Err(AstError {
            span: Span::new(0..3),
            kind: AstErrorKind::FlagUnrecognized { flag: '☃' },
        }));
    }
}
