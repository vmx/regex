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
    stack: RefCell<Vec<State>>,
}

enum State {
    /// This state is pushed whenever an opening group is found.
    Group {
        /// The concatenation immediately preceding the opening group.
        concat: AstConcat,
        /// The group that has been opened. Its sub-AST is always empty.
        group: AstGroup,
    },
    /// This state is pushed whenever a new alternation branch is found. If
    /// an alternation branch is found and this state is at the top of the
    /// stack, then this state should be modified to include the new
    /// alternation.
    Alternation(AstAlternation),
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
    fn state_push(&self, x: State) {
        self.stack.borrow_mut().push(x);
    }

    /// Pop an AST from the parser's internal stack.
    ///
    /// If the stack is empty, then `None` is returned.
    fn state_pop(&self) -> Option<State> {
        self.stack.borrow_mut().pop()
    }

    /// Parse and push a group AST (and its parent concatenation) on to the
    /// parser's internal stack. Return a fresh concatenation corresponding
    /// to the group's sub-AST.
    ///
    /// If a set of flags was found (with no group), then the concatenation
    /// is returned with that set of flags added.
    ///
    /// This assumes that the parser is currently positioned on the opening
    /// parenthesis. It advances the parser to the character before the start
    /// of the sub-expression (or adjoining expression).
    ///
    /// If there was a problem parsing the start of the group, then an error
    /// is returned.
    fn push_group(&self, mut concat: AstConcat) -> Result<AstConcat> {
        match try!(self.parse_group()) {
            Either::Left(set) => {
                concat.asts.push(Ast::Flags(set));
                Ok(concat)
            }
            Either::Right(group) => {
                self.state_push(State::Group {
                    concat: concat,
                    group: group,
                });
                // We want our span for the group's AST to start at the first
                // possible position of its sub-expression, which is at the
                // end of the current character.
                let start = self.span_char().end;
                Ok(AstConcat {
                    span: Span::new(start..start),
                    asts: vec![],
                })
            }
        }
    }

    /// Pop a group AST from the parser's internal stack and set the group's
    /// AST to the given concatenation. Return the concatenation containing
    /// the group.
    ///
    /// This assumes that the parser is currently positioned on the closing
    /// parenthesis and does not advance the parser.
    ///
    /// If no such group could be popped, then an unopened group error is
    /// returned.
    fn pop_group(&self, mut group_concat: AstConcat) -> Result<AstConcat> {
        let (mut prior_concat, mut group, alt) =
            match self.state_pop() {
                Some(State::Group { concat, group }) => {
                    (concat, group, None)
                }
                Some(State::Alternation(alt)) => {
                    match self.state_pop() {
                        Some(State::Group { concat, group }) => {
                            (concat, group, Some(alt))
                        }
                        _ => return Err(AstError {
                            span: self.span_char(),
                            kind: AstErrorKind::GroupUnopened,
                        }),
                    }
                }
                _ => return Err(AstError {
                    span: self.span_char(),
                    kind: AstErrorKind::GroupUnopened,
                }),
            };
        group_concat.span.end = self.pos();
        group.span.end = self.span_char().end;
        match alt {
            Some(mut alt) => {
                alt.asts.push(group_concat.into_ast());
                group.ast = Box::new(alt.into_ast());
            }
            None => {
                group.ast = Box::new(group_concat.into_ast());
            }
        }
        prior_concat.asts.push(Ast::Group(group));
        Ok(prior_concat)
    }

    /// Pop the last state from the parser's internal stack, if it exists, and
    /// add the given concatenation to it. There either must be no state or a
    /// single alternation item on the stack. Any other scenario produces an
    /// error.
    ///
    /// This assumes that the parser has advanced to the end.
    fn pop_end(&self, mut concat: AstConcat) -> Result<Ast> {
        concat.span.end = self.pos();
        match self.state_pop() {
            None => Ok(concat.into_ast()),
            Some(State::Alternation(mut alt)) => {
                alt.asts.push(concat.into_ast());
                Ok(Ast::Alternation(alt))
            }
            Some(State::Group { group, .. }) => {
                Err(AstError {
                    span: group.span,
                    kind: AstErrorKind::GroupUnclosed,
                })
            }
        }
    }
}

impl<'s> Parser<'s> {
    /// Parse the regular expression.
    fn parse(&self) -> Result<Ast> {
        if self.is_eof() {
            return Ok(Ast::EmptyString(self.span()));
        }
        let mut concat = AstConcat {
            span: self.span(),
            asts: vec![],
        };
        loop {
            match self.char() {
                '(' => concat = try!(self.push_group(concat)),
                ')' => concat = try!(self.pop_group(concat)),
                _ => unreachable!(),
            }
            if !self.bump() {
                break;
            }
        }
        self.pop_end(concat)
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
                ast: Box::new(Ast::EmptyString(Span {
                    start: self.span_char().end,
                    end: self.span_char().end,
                })),
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

        assert_eq!(parser("()").parse(), Ok(Ast::Group(AstGroup {
            span: Span::new(0..2),
            kind: AstGroupKind::CaptureIndex,
            ast: Box::new(Ast::EmptyString(Span::new(1..1))),
        })));
        assert_eq!(parser("(())").parse(), Ok(Ast::Group(AstGroup {
            span: Span::new(0..4),
            kind: AstGroupKind::CaptureIndex,
            ast: Box::new(Ast::Group(AstGroup {
                span: Span::new(1..3),
                kind: AstGroupKind::CaptureIndex,
                ast: Box::new(Ast::EmptyString(Span::new(2..2))),
            })),
        })));

        assert_eq!(parser("(").parse(), Err(AstError {
            span: Span::new(0..1),
            kind: AstErrorKind::GroupUnclosed,
        }));
        assert_eq!(parser("(()").parse(), Err(AstError {
            span: Span::new(0..1),
            kind: AstErrorKind::GroupUnclosed,
        }));
        assert_eq!(parser(")").parse(), Err(AstError {
            span: Span::new(0..1),
            kind: AstErrorKind::GroupUnopened,
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
