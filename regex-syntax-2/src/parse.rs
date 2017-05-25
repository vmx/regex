use std::cell::{Cell, RefCell};
use std::result;

use ast::*;

type Result<T> = result::Result<T, AstError>;

/// A simple binary sum type.
///
/// This is occasionally useful in the parser in an ad hoc fashion.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Either<Left, Right> {
    Left(Left),
    Right(Right),
}

/// A primitive is an expression with no sub-expressions. This includes
/// literals, assertions and non-set character classes.
///
/// This does not include ASCII character classes, since they can only appear
/// within a set character class.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Primitive {
    Literal(AstLiteral),
    Assertion(AstAssertion),
    Dot(Span),
    Perl(AstClassPerl),
    Unicode(AstClassUnicode),
}

impl Primitive {
    fn into_ast(self) -> Ast {
        match self {
            Primitive::Literal(lit) => Ast::Literal(lit),
            Primitive::Assertion(assert) => Ast::Assertion(assert),
            Primitive::Dot(span) => Ast::Class(AstClass::Dot(span)),
            Primitive::Perl(cls) => Ast::Class(AstClass::Perl(cls)),
            Primitive::Unicode(cls) => Ast::Class(AstClass::Unicode(cls)),
        }
    }
}

/// Returns true if the give character has significance in a regex.
///
/// These are the only characters that are allowed to be escaped.
fn is_punct(c: char) -> bool {
    match c {
        '\\' | '.' | '+' | '*' | '?' | '(' | ')' | '|' |
        '[' | ']' | '{' | '}' | '^' | '$' | '#' | '&' | '-' | '~' => true,
        _ => false,
    }
}

/// Returns true if the given character is a hexadecimal digit.
fn is_hex(c: char) -> bool {
    ('0' <= c && c <= '9') || ('a' <= c && c <= 'f') || ('A' <= c && c <= 'F')
}

/// Returns true if the given character is a valid in a capture group name.
///
/// If `first` is true, then `c` is treated as the first character in the
/// group name (which is not allowed to be a digit).
fn is_capture_char(c: char, first: bool) -> bool {
    c == '_' || (!first && c >= '0' && c <= '9')
    || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
}

/// A regular expression parser.
///
/// This parses a string representation of a regular expression into an
/// abstract syntax tree.
pub struct Parser<'p> {
    /// The full regular expression provided by the user.
    pattern: &'p str,
    /// The current position of the parser.
    coffset: Cell<usize>,
    /// The current line number of the parser.
    cline: Cell<usize>,
    /// The current column number of the parser.
    ccolumn: Cell<usize>,
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

impl State {
    fn is_alternation(&self) -> bool {
        match *self {
            State::Alternation(_) => true,
            _ => false,
        }
    }
}

impl<'p> Parser<'p> {
    /// Create a new parser for the given regular expression.
    pub fn new(pattern: &str) -> Parser {
        Parser {
            pattern: pattern,
            coffset: Cell::new(0),
            cline: Cell::new(1),
            ccolumn: Cell::new(1),
            stack: RefCell::new(vec![]),
        }
    }

    /// Return the current offset of the parser.
    ///
    /// The offset starts at `0` from the beginning of the regular expression
    /// pattern string.
    fn offset(&self) -> usize {
        self.coffset.get()
    }

    /// Return the current line number of the parser.
    ///
    /// The line number starts at `1`.
    fn line(&self) -> usize {
        self.cline.get()
    }

    /// Return the current column of the parser.
    ///
    /// The column number starts at `1` and is reset whenever a `\n` is seen.
    fn column(&self) -> usize {
        self.ccolumn.get()
    }

    /// Return the character at the current position of the parser.
    ///
    /// This panics if the current position does not point to a valid char.
    fn char(&self) -> char {
        self.char_at(self.offset())
    }

    /// Return the character at the given position.
    ///
    /// This panics if the given position does not point to a valid char.
    fn char_at(&self, i: usize) -> char {
        self.pattern[i..].chars().next()
            .expect(&format!("expected char at offset {}", i))
    }

    /// Bump the parser to the next Unicode scalar value.
    ///
    /// If the end of the input has been reached, then `false` is returned.
    fn bump(&self) -> bool {
        if self.char() == '\n' {
            self.ccolumn.set(1);
            self.cline.set(self.line().checked_add(1).unwrap());
        } else {
            self.ccolumn.set(self.column().checked_add(1).unwrap());
        }
        self.coffset.set(self.offset() + self.char().len_utf8());
        self.pattern[self.coffset.get()..].chars().next().is_some()
    }

    /// If the substring starting at the current position of the parser has
    /// the given prefix, then bump the parser to the character immediately
    /// following the prefix and return true. Otherwise, don't bump the parser
    /// and return false.
    fn bump_if(&self, prefix: &str) -> bool {
        if self.pattern[self.offset()..].starts_with(prefix) {
            for _ in 0..prefix.chars().count() {
                self.bump();
            }
            true
        } else {
            false
        }
    }

    /// Peek at the next character in the input without advancing the parser.
    ///
    /// If the input has been exhausted, then this returns `None`.
    fn peek(&self) -> Option<char> {
        self.pattern[self.offset() + self.char().len_utf8()..].chars().next()
    }

    /// Returns true if the next call to `bump` would return false.
    fn is_eof(&self) -> bool {
        self.offset() == self.pattern.len()
    }

    /// Return the current position of the parser, which includes the offset,
    /// line and column.
    fn pos(&self) -> Position {
        Position::new(self.offset(), self.line(), self.column())
    }

    /// Create a span at the current position of the parser. Both the start
    /// and end of the span are set.
    fn span(&self) -> Span {
        Span::splat(self.pos())
    }

    /// Create a span that covers the current character.
    fn span_char(&self) -> Span {
        let mut next = Position {
            offset: self.offset().checked_add(self.char().len_utf8()).unwrap(),
            line: self.line(),
            column: self.column().checked_add(1).unwrap(),
        };
        if self.char() == '\n' {
            next.line += 1;
            next.column = 1;
        }
        Span::new(self.pos(), next)
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

    /// Parse and push a repetition operator on to the given concatenation.
    /// The operator is applied to the last AST in the concatenation. If the
    /// concatenation is empty, then the operator is applied to the empty AST.
    ///
    /// This assumes the parser is currently positioned at the repetition
    /// operator (?, * or +) and advances the parser to the first character
    /// after the operator.
    fn push_repetition(
        &self,
        mut concat: AstConcat,
        kind: AstRepetitionKind,
    ) -> AstConcat {
        assert!(self.char() == '?'
                || self.char() == '*'
                || self.char() == '+');
        let ast = match concat.asts.pop() {
            None => Ast::Empty(self.span()),
            Some(ast) => ast,
        };
        let mut greedy = true;
        if self.bump() && self.char() == '?' {
            greedy = false;
            self.bump();
        }
        concat.asts.push(Ast::Repetition(AstRepetition {
            span: ast.span().with_end(self.pos()),
            kind: kind,
            greedy: greedy,
            ast: Box::new(ast),
        }));
        concat
    }

    /// Parse and push a single alternation on to the parser's internal stack.
    /// If the top of the stack already has an alternation, then add to that
    /// instead of pushing a new one.
    ///
    /// The concatenation given corresponds to a single alternation branch.
    /// The concatenation returned starts the next branch and is empty.
    ///
    /// This assumes the parser is currently positioned at `|` and will advance
    /// the parser to the character following `|`.
    fn push_alternate(&self, mut concat: AstConcat) -> Result<AstConcat> {
        assert_eq!(self.char(), '|');
        concat.span.end = self.pos();
        self.push_or_add_alternation(concat);
        self.bump();
        Ok(AstConcat {
            span: self.span(),
            asts: vec![],
        })
    }

    /// Pushes or adds the given branch of an alternation to the parser's
    /// internal stack of state.
    fn push_or_add_alternation(&self, concat: AstConcat) {
        let mut stack = self.stack.borrow_mut();
        if let Some(&mut State::Alternation(ref mut alts)) = stack.last_mut() {
            alts.asts.push(concat.into_ast());
            return;
        }
        stack.push(State::Alternation(AstAlternation {
            span: Span::new(concat.span.start, self.pos()),
            asts: vec![concat.into_ast()],
        }));
    }

    /// Parse and push a group AST (and its parent concatenation) on to the
    /// parser's internal stack. Return a fresh concatenation corresponding
    /// to the group's sub-AST.
    ///
    /// If a set of flags was found (with no group), then the concatenation
    /// is returned with that set of flags added.
    ///
    /// This assumes that the parser is currently positioned on the opening
    /// parenthesis. It advances the parser to the character at the start
    /// of the sub-expression (or adjoining expression).
    ///
    /// If there was a problem parsing the start of the group, then an error
    /// is returned.
    fn push_group(&self, mut concat: AstConcat) -> Result<AstConcat> {
        assert_eq!(self.char(), '(');
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
                Ok(AstConcat {
                    span: self.span(),
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
    /// parenthesis and advances the parser to the character following the `)`.
    ///
    /// If no such group could be popped, then an unopened group error is
    /// returned.
    fn pop_group(&self, mut group_concat: AstConcat) -> Result<AstConcat> {
        assert_eq!(self.char(), ')');
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
        self.bump();
        group.span.end = self.pos();
        match alt {
            Some(mut alt) => {
                alt.span.end = group_concat.span.end;
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
        let ast = match self.state_pop() {
            None => Ok(concat.into_ast()),
            Some(State::Alternation(mut alt)) => {
                alt.span.end = self.pos();
                alt.asts.push(concat.into_ast());
                Ok(Ast::Alternation(alt))
            }
            Some(State::Group { group, .. }) => {
                return Err(AstError {
                    span: group.span,
                    kind: AstErrorKind::GroupUnclosed,
                });
            }
        };
        // If we try to pop again, there should be nothing.
        match self.state_pop() {
            None => ast,
            Some(State::Alternation(_)) => {
                // This unreachable (the only one in the entire parser) is
                // unfortunate. This case can't happen because the only way
                // we can be here is if there were two `State::Alternation`s
                // adjacent in the parser's stack, which we guarantee to never
                // happen because we never push a `State::Alternation` if one
                // is already at the top of the stack.
                unreachable!()
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
            return Ok(Ast::Empty(self.span()));
        }
        let mut concat = AstConcat {
            span: self.span(),
            asts: vec![],
        };
        // BREADCRUMBS:
        //
        // Three key things left to do:
        //
        // x 1. Alternations (mostly done at this point with parser state).
        // x 2. Repetition operators. Requires looking at current concat.
        //   3. Implement support for (?x).
        //   4. Character classes, including nested classes. Joy.
        while !self.is_eof() {
            match self.char() {
                '(' => concat = try!(self.push_group(concat)),
                ')' => concat = try!(self.pop_group(concat)),
                '|' => concat = try!(self.push_alternate(concat)),
                '?' => {
                    concat = self.push_repetition(
                        concat, AstRepetitionKind::ZeroOrOne);
                }
                '*' => {
                    concat = self.push_repetition(
                        concat, AstRepetitionKind::ZeroOrMore);
                }
                '+' => {
                    concat = self.push_repetition(
                        concat, AstRepetitionKind::OneOrMore);
                }
                _ => concat.asts.push(try!(self.parse_primitive()).into_ast()),
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
                ast: Box::new(Ast::Empty(self.span())),
            }))
        } else if self.bump_if("(?") {
            let flags = try!(self.parse_flags());
            let char_end = self.char();
            self.bump();
            if char_end == ')' {
                Ok(Either::Left(AstSetFlags {
                    span: Span { end: self.pos(), ..open_span },
                    flags: flags,
                }))
            } else {
                assert_eq!(char_end, ':');
                Ok(Either::Right(AstGroup {
                    span: open_span,
                    kind: AstGroupKind::NonCapturing(flags),
                    ast: Box::new(Ast::Empty(self.span())),
                }))
            }
        } else {
            assert_eq!(self.char(), '(');
            self.bump();
            Ok(Either::Right(AstGroup {
                span: open_span,
                kind: AstGroupKind::CaptureIndex,
                ast: Box::new(Ast::Empty(self.span())),
            }))
        }
    }

    /// Parses a capture group name. Assumes that the parser is positioned at
    /// the first character in the name following the opening `<` (and may
    /// possibly be EOF). This advances the parser to the first character
    /// following the closing `>`.
    fn parse_capture_name(&self) -> Result<AstCaptureName> {
        if self.is_eof() {
            return Err(AstError {
                span: self.span(),
                kind: AstErrorKind::GroupNameUnexpectedEof,
            });
        }
        let start = self.pos();
        loop {
            if self.char() == '>' {
                break;
            }
            if !is_capture_char(self.char(), self.pos() == start) {
                return Err(AstError {
                    span: self.span_char(),
                    kind: AstErrorKind::GroupNameInvalid { c: self.char() },
                });
            }
            if !self.bump() {
                break;
            }
        }
        let end = self.pos();
        if self.is_eof() {
            return Err(AstError {
                span: self.span(),
                kind: AstErrorKind::GroupNameUnexpectedEof,
            });
        }
        assert_eq!(self.char(), '>');
        self.bump();
        let name = &self.pattern[start.offset..end.offset];
        if name.is_empty() {
            return Err(AstError {
                span: Span::new(start, start),
                kind: AstErrorKind::GroupNameEmpty,
            });
        }
        Ok(AstCaptureName {
            span: Span::new(start, end),
            name: name.to_string(),
        })
    }

    /// Parse a sequence of flags starting at the current character.
    ///
    /// This advances the parser to the character immediately following the
    /// flags, which is guaranteed to be either `:` or `)`.
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
        Ok(flags)
    }

    /// Parse the current character as a flag. Do not advance the parser.
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

    /// Parse a primitive AST. e.g., A literal, non-set character class or
    /// assertion.
    ///
    /// This assumes that the parser expects a primitive at the current
    /// location. i.e., All other non-primitive cases have been handled.
    /// For example, if the parser's position is at `|`, then `|` will be
    /// treated as a literal (e.g., inside a character class).
    ///
    /// This advances the parser to the first character immediately following
    /// the primitive.
    fn parse_primitive(&self) -> Result<Primitive> {
        match self.char() {
            '\\' => self.parse_escape(),
            '.' => {
                let ast = Primitive::Dot(self.span_char());
                self.bump();
                Ok(ast)
            }
            '^' => {
                let ast = Primitive::Assertion(AstAssertion {
                    span: self.span_char(),
                    kind: AstAssertionKind::StartLine,
                });
                self.bump();
                Ok(ast)
            }
            '$' => {
                let ast = Primitive::Assertion(AstAssertion {
                    span: self.span_char(),
                    kind: AstAssertionKind::EndLine,
                });
                self.bump();
                Ok(ast)
            }
            c => {
                let ast = Primitive::Literal(AstLiteral {
                    span: self.span_char(),
                    kind: AstLiteralKind::Verbatim,
                    c: c,
                });
                self.bump();
                Ok(ast)
            }
        }
    }

    /// Parse an escape sequence as a primitive AST.
    ///
    /// This assumes the parser is positioned at the start of the escape
    /// sequence, i.e., `\`. It advances the parser to the first character
    /// immediately following the escape sequence.
    fn parse_escape(&self) -> Result<Primitive> {
        assert_eq!(self.char(), '\\');
        let start = self.pos();
        if !self.bump() {
            return Err(AstError {
                span: Span::new(start, self.pos()),
                kind: AstErrorKind::EscapeUnexpectedEof,
            });
        }
        let c = self.char();
        // Put some of the more complicated routines into helpers.
        match c {
            '0'...'7' => {
                let mut lit = self.parse_octal();
                lit.span.start = start;
                return Ok(Primitive::Literal(lit));
            }
            'x' => {
                let mut lit = try!(self.parse_hex());
                lit.span.start = start;
                return Ok(Primitive::Literal(lit));
            }
            'p' | 'P' => {
                let mut cls = try!(self.parse_unicode_class());
                cls.span.start = start;
                return Ok(Primitive::Unicode(cls));
            }
            'd' | 's' | 'w' | 'D' | 'S' | 'W' => {
                let mut cls = self.parse_perl_class();
                cls.span.start = start;
                return Ok(Primitive::Perl(cls));
            }
            _ => {}
        }

        // Handle all of the one letter sequences inline.
        self.bump();
        let span = Span::new(start, self.pos());
        if is_punct(c) {
            return Ok(Primitive::Literal(AstLiteral {
                span: span,
                kind: AstLiteralKind::Punctuation,
                c: c,
            }));
        }
        let special = |c| Ok(Primitive::Literal(AstLiteral {
            span: span,
            kind: AstLiteralKind::Special,
            c: c,
        }));
        match c {
            'a' => special('\x07'),
            'f' => special('\x0C'),
            't' => special('\t'),
            'n' => special('\n'),
            'r' => special('\r'),
            'v' => special('\x0B'),
            'A' => Ok(Primitive::Assertion(AstAssertion {
                span: span,
                kind: AstAssertionKind::StartText,
            })),
            'z' => Ok(Primitive::Assertion(AstAssertion {
                span: span,
                kind: AstAssertionKind::EndText,
            })),
            'b' => Ok(Primitive::Assertion(AstAssertion {
                span: span,
                kind: AstAssertionKind::WordBoundary,
            })),
            'B' => Ok(Primitive::Assertion(AstAssertion {
                span: span,
                kind: AstAssertionKind::NotWordBoundary,
            })),
            c => Err(AstError {
                span: span,
                kind: AstErrorKind::EscapeUnrecognized { c: c },
            }),
        }
    }

    /// Parse an octal representation of a Unicode codepoint up to 3 digits
    /// long. This expects the parser to be positioned at the first octal
    /// digit and advances the parser to the first character immediately
    /// following the octal number.
    ///
    /// This routine can never fail.
    fn parse_octal(&self) -> AstLiteral {
        use std::char;
        use std::u32;

        assert!('0' <= self.char() && self.char() <= '7');
        let start = self.pos();
        // Parse up to two more digits.
        while
            self.bump() &&
            '0' <= self.char() && self.char() <= '7' &&
            self.pos().offset - start.offset <= 2
        {}
        let end = self.pos();
        let octal = &self.pattern[start.offset..end.offset];
        // Parsing the octal should never fail since the above guarantees a
        // valid number.
        let codepoint =
            u32::from_str_radix(octal, 8).expect("valid octal number");
        // The max value for 3 digit octal is 0777 = 511 and [0, 511] has no
        // invalid Unicode scalar values.
        let c = char::from_u32(codepoint).expect("Unicode scalar value");
        AstLiteral {
            span: Span::new(start, end),
            kind: AstLiteralKind::Octal,
            c: c,
        }
    }

    /// Parse a hex representation of a Unicode codepoint. This handles both
    /// hex notations, i.e., `\xFF` and `\x{FFFF}`. This expects the parser to
    /// be positioned at the `x`. The parser is advanced to the first character
    /// immediately following the hexadecimal literal.
    fn parse_hex(&self) -> Result<AstLiteral> {
        assert_eq!(self.char(), 'x');
        if !self.bump() {
            return Err(AstError {
                span: self.span(),
                kind: AstErrorKind::EscapeUnexpectedEof,
            });
        }
        if self.char() == '{' {
            self.parse_hex_brace()
        } else {
            self.parse_hex_two()
        }
    }

    /// Parse a two digit hex representation of a Unicode codepoint. This
    /// expects the parser to be positioned at the first digit and will advance
    /// the parser to the first character immediately following the escape
    /// sequence.
    fn parse_hex_two(&self) -> Result<AstLiteral> {
        use std::char;
        use std::u32;

        let start = self.pos();
        assert!(is_hex(self.char()));
        if !self.bump() {
            return Err(AstError {
                span: self.span(),
                kind: AstErrorKind::EscapeUnexpectedEof,
            });
        }
        if !is_hex(self.char()) {
            return Err(AstError {
                span: self.span_char(),
                kind: AstErrorKind::EscapeHexInvalidDigit {
                    c: self.char(),
                },
            });
        }
        self.bump();
        let end = self.pos();
        let hex = &self.pattern[start.offset..end.offset];
        // The above checks guarantee a valid hexadecimal literal.
        let codepoint =
            u32::from_str_radix(hex, 16).expect("valid hex number");
        // The max value for a two digit hex literal is 0xFF and [0, 0xFF]
        // has no invalid Unicode scalar values.
        let c = char::from_u32(codepoint).expect("Unicode scalar value");
        Ok(AstLiteral {
            span: Span::new(start, end),
            kind: AstLiteralKind::Hex,
            c: c,
        })
    }

    /// Parse a hex representation of any Unicode scalar value. This expects
    /// the parser to be positioned at the opening brace `{` and will advance
    /// the parser to the first character following the closing brace `}`.
    fn parse_hex_brace(&self) -> Result<AstLiteral> {
        use std::char;
        use std::u32;

        let brace_pos = self.pos();
        let start = self.span_char().end;
        while self.bump() && self.char() != '}' {
            if !is_hex(self.char()) {
                return Err(AstError {
                    span: self.span_char(),
                    kind: AstErrorKind::EscapeHexInvalidDigit {
                        c: self.char(),
                    },
                });
            }
        }
        if self.is_eof() {
            return Err(AstError {
                span: Span::new(brace_pos, self.pos()),
                kind: AstErrorKind::EscapeUnexpectedEof,
            })
        }
        let end = self.pos();
        let hex = &self.pattern[start.offset..end.offset];
        assert_eq!(self.char(), '}');
        self.bump();

        if hex.is_empty() {
            return Err(AstError {
                span: Span::new(brace_pos, self.pos()),
                kind: AstErrorKind::EscapeHexEmpty,
            })
        }
        match u32::from_str_radix(hex, 16).ok().and_then(char::from_u32) {
            None => Err(AstError {
                span: Span::new(start, end),
                kind: AstErrorKind::EscapeHexInvalid,
            }),
            Some(c) => Ok(AstLiteral {
                span: Span::new(start, self.pos()),
                kind: AstLiteralKind::Unicode,
                c: c,
            }),
        }
    }

    /// Parse a Unicode class in either the single character notation, `\pN`
    /// or the multi-character bracketed notation, `\p{Greek}`. This assumes
    /// the parser is positioned at the `p` (or `P` for negation) and will
    /// advance the parser to the character immediately following the class.
    ///
    /// Note that this does not check whether the class name is valid or not.
    fn parse_unicode_class(&self) -> Result<AstClassUnicode> {
        assert!(self.char() == 'p' || self.char() == 'P');
        let negated = self.char() == 'P';
        if !self.bump() {
            return Err(AstError {
                span: self.span(),
                kind: AstErrorKind::EscapeUnexpectedEof,
            });
        }
        let (start, end, kind) =
            if self.char() == '{' {
                let start = self.span_char().end;
                while self.bump() && self.char() != '}' {}
                if self.is_eof() {
                    return Err(AstError {
                        span: self.span(),
                        kind: AstErrorKind::EscapeUnexpectedEof,
                    });
                }
                assert_eq!(self.char(), '}');
                let end = self.pos();
                self.bump();
                (start, end, AstClassUnicodeKind::Bracketed)
            } else {
                let start = self.pos();
                self.bump();
                (start, self.pos(), AstClassUnicodeKind::OneLetter)
            };
        Ok(AstClassUnicode {
            span: Span::new(start, self.pos()),
            kind: kind,
            negated: negated,
            name: self.pattern[start.offset..end.offset].to_string(),
        })
    }

    /// Parse a Perl character class, e.g., `\d` or `\W`. This assumes the
    /// parser is currently at a valid character class name and will be
    /// advanced to the character immediately following the class.
    fn parse_perl_class(&self) -> AstClassPerl {
        let c = self.char();
        let span = self.span_char();
        self.bump();
        let (negated, kind) = match c {
            'd' => (false, AstClassPerlKind::Digit),
            'D' => (true, AstClassPerlKind::Digit),
            's' => (false, AstClassPerlKind::Space),
            'S' => (true, AstClassPerlKind::Space),
            'w' => (false, AstClassPerlKind::Word),
            'W' => (true, AstClassPerlKind::Word),
            c => panic!("expected valid Perl class but got '{}'", c),
        };
        AstClassPerl { span: span, kind: kind, negated: negated }
    }
}

#[cfg(test)]
mod tests {
    use std::ops::Range;

    use ast::*;
    use super::{Parser, Primitive};

    fn parser(pattern: &str) -> Parser {
        Parser::new(pattern)
    }

    /// Create a new span from the given offset range. This assumes a single
    /// line and sets the columns based on the offsets. i.e., This only works
    /// out of the box for ASCII, which is fine for most tests.
    fn span(range: Range<usize>) -> Span {
        let start = Position::new(range.start, 1, range.start + 1);
        let end = Position::new(range.end, 1, range.end + 1);
        Span::new(start, end)
    }

    /// Create a new span starting at the given offset/column and ending where
    /// the given string ends.
    fn span_with(start: usize, ending_at: &str) -> Span {
        let start = Position::new(start, 1, start + 1);
        let end = Position {
            offset: start.offset + ending_at.len(),
            line: start.line + ending_at.matches('\n').count(),
            column: start.column + ending_at.chars().count(),
        };
        Span::new(start, end)
    }

    /// Create a new span for the corresponding byte range in the given string.
    fn span_range(subject: &str, start: usize, end: usize) -> Span {
        let start = Position {
            offset: start,
            line: 1 + subject[..start].matches('\n').count(),
            column: 1 + subject[..start]
                .as_bytes()
                .iter()
                .rev()
                .position(|&b| b == b'\n')
                .unwrap_or(start),
        };
        let end = Position {
            offset: end,
            line: 1 + subject[..end].matches('\n').count(),
            column: 1 + subject[..end]
                .as_bytes()
                .iter()
                .rev()
                .position(|&b| b == b'\n')
                .unwrap_or(end),
        };
        Span::new(start, end)
    }

    /// Create a verbatim literal starting at the given position.
    fn lit(c: char, start: usize) -> Ast {
        lit_with(c, span(start..start + c.len_utf8()))
    }

    /// Create a verbatim literal with the given span.
    fn lit_with(c: char, span: Span) -> Ast {
        Ast::Literal(AstLiteral {
            span: span,
            kind: AstLiteralKind::Verbatim,
            c: c,
        })
    }

    /// Create a concatenation with the given range.
    fn concat(range: Range<usize>, asts: Vec<Ast>) -> Ast {
        concat_with(span(range), asts)
    }

    /// Create a concatenation with the given span.
    fn concat_with(span: Span, asts: Vec<Ast>) -> Ast {
        Ast::Concat(AstConcat { span: span, asts: asts })
    }

    /// Create an alternation with the given span.
    fn alt(range: Range<usize>, asts: Vec<Ast>) -> Ast {
        Ast::Alternation(AstAlternation { span: span(range), asts: asts })
    }

    /// Create a capturing group with the given span.
    fn group(range: Range<usize>, ast: Ast) -> Ast {
        Ast::Group(AstGroup {
            span: span(range),
            kind: AstGroupKind::CaptureIndex,
            ast: Box::new(ast),
        })
    }

    #[test]
    fn parse_newlines() {
        let pat = ".\n.";
        assert_eq!(
            parser(pat).parse(),
            Ok(concat_with(span_range(pat, 0, 3), vec![
                Ast::Class(AstClass::Dot(span_range(pat, 0, 1))),
                lit_with('\n', span_range(pat, 1, 2)),
                Ast::Class(AstClass::Dot(span_range(pat, 2, 3))),
            ])));
    }

    #[test]
    fn parse_repetition() {
        assert_eq!(
            parser(r"*").parse(),
            Ok(Ast::Repetition(AstRepetition {
                span: span(0..1),
                kind: AstRepetitionKind::ZeroOrMore,
                greedy: true,
                ast: Box::new(Ast::Empty(span(0..0))),
            })));
        assert_eq!(
            parser(r"+").parse(),
            Ok(Ast::Repetition(AstRepetition {
                span: span(0..1),
                kind: AstRepetitionKind::OneOrMore,
                greedy: true,
                ast: Box::new(Ast::Empty(span(0..0))),
            })));

        assert_eq!(
            parser(r"?").parse(),
            Ok(Ast::Repetition(AstRepetition {
                span: span(0..1),
                kind: AstRepetitionKind::ZeroOrOne,
                greedy: true,
                ast: Box::new(Ast::Empty(span(0..0))),
            })));
        assert_eq!(
            parser(r"??").parse(),
            Ok(Ast::Repetition(AstRepetition {
                span: span(0..2),
                kind: AstRepetitionKind::ZeroOrOne,
                greedy: false,
                ast: Box::new(Ast::Empty(span(0..0))),
            })));
        assert_eq!(
            parser(r"a?").parse(),
            Ok(Ast::Repetition(AstRepetition {
                span: span(0..2),
                kind: AstRepetitionKind::ZeroOrOne,
                greedy: true,
                ast: Box::new(lit('a', 0)),
            })));
        assert_eq!(
            parser(r"a?b").parse(),
            Ok(concat(0..3, vec![
                Ast::Repetition(AstRepetition {
                    span: span(0..2),
                    kind: AstRepetitionKind::ZeroOrOne,
                    greedy: true,
                    ast: Box::new(lit('a', 0)),
                }),
                lit('b', 2),
            ])));
        assert_eq!(
            parser(r"a??b").parse(),
            Ok(concat(0..4, vec![
                Ast::Repetition(AstRepetition {
                    span: span(0..3),
                    kind: AstRepetitionKind::ZeroOrOne,
                    greedy: false,
                    ast: Box::new(lit('a', 0)),
                }),
                lit('b', 3),
            ])));
        assert_eq!(
            parser(r"ab?").parse(),
            Ok(concat(0..3, vec![
                lit('a', 0),
                Ast::Repetition(AstRepetition {
                    span: span(1..3),
                    kind: AstRepetitionKind::ZeroOrOne,
                    greedy: true,
                    ast: Box::new(lit('b', 1)),
                }),
            ])));
        assert_eq!(
            parser(r"(ab)?").parse(),
            Ok(Ast::Repetition(AstRepetition {
                span: span(0..5),
                kind: AstRepetitionKind::ZeroOrOne,
                greedy: true,
                ast: Box::new(group(0..4, concat(1..3, vec![
                    lit('a', 1),
                    lit('b', 2),
                ]))),
            })));
        assert_eq!(
            parser(r"|?").parse(),
            Ok(alt(0..2, vec![
                Ast::Empty(span(0..0)),
                Ast::Repetition(AstRepetition {
                    span: span(1..2),
                    kind: AstRepetitionKind::ZeroOrOne,
                    greedy: true,
                    ast: Box::new(Ast::Empty(span(1..1))),
                }),
            ])));
    }

    #[test]
    fn parse_alternate() {
        assert_eq!(
            parser(r"a|b").parse(),
            Ok(Ast::Alternation(AstAlternation {
                span: span(0..3),
                asts: vec![lit('a', 0), lit('b', 2)],
            })));
        assert_eq!(
            parser(r"(a|b)").parse(),
            Ok(group(0..5, Ast::Alternation(AstAlternation {
                span: span(1..4),
                asts: vec![lit('a', 1), lit('b', 3)],
            }))));

        assert_eq!(
            parser(r"a|b|c").parse(),
            Ok(Ast::Alternation(AstAlternation {
                span: span(0..5),
                asts: vec![lit('a', 0), lit('b', 2), lit('c', 4)],
            })));
        assert_eq!(
            parser(r"ax|by|cz").parse(),
            Ok(Ast::Alternation(AstAlternation {
                span: span(0..8),
                asts: vec![
                    concat(0..2, vec![lit('a', 0), lit('x', 1)]),
                    concat(3..5, vec![lit('b', 3), lit('y', 4)]),
                    concat(6..8, vec![lit('c', 6), lit('z', 7)]),
                ],
            })));
        assert_eq!(
            parser(r"(ax|by|cz)").parse(),
            Ok(group(0..10, Ast::Alternation(AstAlternation {
                span: span(1..9),
                asts: vec![
                    concat(1..3, vec![lit('a', 1), lit('x', 2)]),
                    concat(4..6, vec![lit('b', 4), lit('y', 5)]),
                    concat(7..9, vec![lit('c', 7), lit('z', 8)]),
                ],
            }))));
        assert_eq!(
            parser(r"(ax|(by|(cz)))").parse(),
            Ok(group(0..14, alt(1..13, vec![
                concat(1..3, vec![lit('a', 1), lit('x', 2)]),
                group(4..13, alt(5..12, vec![
                    concat(5..7, vec![lit('b', 5), lit('y', 6)]),
                    group(8..12, concat(9..11, vec![
                        lit('c', 9),
                        lit('z', 10),
                    ])),
                ])),
            ]))));

        assert_eq!(
            parser(r"|").parse(), Ok(alt(0..1, vec![
                Ast::Empty(span(0..0)), Ast::Empty(span(1..1)),
            ])));
        assert_eq!(
            parser(r"||").parse(), Ok(alt(0..2, vec![
                Ast::Empty(span(0..0)),
                Ast::Empty(span(1..1)),
                Ast::Empty(span(2..2)),
            ])));
        assert_eq!(
            parser(r"a|").parse(), Ok(alt(0..2, vec![
                lit('a', 0), Ast::Empty(span(2..2)),
            ])));
        assert_eq!(
            parser(r"|a").parse(), Ok(alt(0..2, vec![
                Ast::Empty(span(0..0)), lit('a', 1),
            ])));

        assert_eq!(
            parser(r"(|)").parse(), Ok(group(0..3, alt(1..2, vec![
                Ast::Empty(span(1..1)), Ast::Empty(span(2..2)),
            ]))));
        assert_eq!(
            parser(r"(a|)").parse(), Ok(group(0..4, alt(1..3, vec![
                lit('a', 1), Ast::Empty(span(3..3)),
            ]))));
        assert_eq!(
            parser(r"(|a)").parse(), Ok(group(0..4, alt(1..3, vec![
                Ast::Empty(span(1..1)), lit('a', 2),
            ]))));

        assert_eq!(
            parser(r"a|b)").parse(), Err(AstError {
                span: span(3..4),
                kind: AstErrorKind::GroupUnopened,
            }));
        assert_eq!(
            parser(r"(a|b").parse(), Err(AstError {
                span: span(0..1),
                kind: AstErrorKind::GroupUnclosed,
            }));
    }

    #[test]
    fn parse_group() {
        assert_eq!(parser("(?i)").parse(), Ok(Ast::Flags(AstSetFlags {
            span: span(0..4),
            flags: AstFlags {
                span: span(2..3),
                items: vec![AstFlagsItem {
                    span: span(2..3),
                    kind: AstFlagsItemKind::Flag(AstFlag::CaseInsensitive),
                }],
            },
        })));
        assert_eq!(parser("(?iU)").parse(), Ok(Ast::Flags(AstSetFlags {
            span: span(0..5),
            flags: AstFlags {
                span: span(2..4),
                items: vec![
                    AstFlagsItem {
                        span: span(2..3),
                        kind: AstFlagsItemKind::Flag(AstFlag::CaseInsensitive),
                    },
                    AstFlagsItem {
                        span: span(3..4),
                        kind: AstFlagsItemKind::Flag(AstFlag::SwapGreed),
                    },
                ],
            },
        })));
        assert_eq!(parser("(?i-U)").parse(), Ok(Ast::Flags(AstSetFlags {
            span: span(0..6),
            flags: AstFlags {
                span: span(2..5),
                items: vec![
                    AstFlagsItem {
                        span: span(2..3),
                        kind: AstFlagsItemKind::Flag(AstFlag::CaseInsensitive),
                    },
                    AstFlagsItem {
                        span: span(3..4),
                        kind: AstFlagsItemKind::Negation,
                    },
                    AstFlagsItem {
                        span: span(4..5),
                        kind: AstFlagsItemKind::Flag(AstFlag::SwapGreed),
                    },
                ],
            },
        })));

        assert_eq!(parser("()").parse(), Ok(Ast::Group(AstGroup {
            span: span(0..2),
            kind: AstGroupKind::CaptureIndex,
            ast: Box::new(Ast::Empty(span(1..1))),
        })));
        assert_eq!(parser("(a)").parse(), Ok(Ast::Group(AstGroup {
            span: span(0..3),
            kind: AstGroupKind::CaptureIndex,
            ast: Box::new(lit('a', 1)),
        })));
        assert_eq!(parser("(())").parse(), Ok(Ast::Group(AstGroup {
            span: span(0..4),
            kind: AstGroupKind::CaptureIndex,
            ast: Box::new(Ast::Group(AstGroup {
                span: span(1..3),
                kind: AstGroupKind::CaptureIndex,
                ast: Box::new(Ast::Empty(span(2..2))),
            })),
        })));

        assert_eq!(parser("(?:a)").parse(), Ok(Ast::Group(AstGroup {
            span: span(0..5),
            kind: AstGroupKind::NonCapturing(AstFlags {
                span: span(2..2),
                items: vec![],
            }),
            ast: Box::new(lit('a', 3)),
        })));

        assert_eq!(parser("(?i:a)").parse(), Ok(Ast::Group(AstGroup {
            span: span(0..6),
            kind: AstGroupKind::NonCapturing(AstFlags {
                span: span(2..3),
                items: vec![
                    AstFlagsItem {
                        span: span(2..3),
                        kind: AstFlagsItemKind::Flag(AstFlag::CaseInsensitive),
                    },
                ],
            }),
            ast: Box::new(lit('a', 4)),
        })));
        assert_eq!(parser("(?i-U:a)").parse(), Ok(Ast::Group(AstGroup {
            span: span(0..8),
            kind: AstGroupKind::NonCapturing(AstFlags {
                span: span(2..5),
                items: vec![
                    AstFlagsItem {
                        span: span(2..3),
                        kind: AstFlagsItemKind::Flag(AstFlag::CaseInsensitive),
                    },
                    AstFlagsItem {
                        span: span(3..4),
                        kind: AstFlagsItemKind::Negation,
                    },
                    AstFlagsItem {
                        span: span(4..5),
                        kind: AstFlagsItemKind::Flag(AstFlag::SwapGreed),
                    },
                ],
            }),
            ast: Box::new(lit('a', 6)),
        })));

        assert_eq!(parser("(").parse(), Err(AstError {
            span: span(0..1),
            kind: AstErrorKind::GroupUnclosed,
        }));
        assert_eq!(parser("(a").parse(), Err(AstError {
            span: span(0..1),
            kind: AstErrorKind::GroupUnclosed,
        }));
        assert_eq!(parser("(()").parse(), Err(AstError {
            span: span(0..1),
            kind: AstErrorKind::GroupUnclosed,
        }));
        assert_eq!(parser(")").parse(), Err(AstError {
            span: span(0..1),
            kind: AstErrorKind::GroupUnopened,
        }));
        assert_eq!(parser("a)").parse(), Err(AstError {
            span: span(1..2),
            kind: AstErrorKind::GroupUnopened,
        }));
    }

    #[test]
    fn parse_capture_name() {
        assert_eq!(parser("(?P<a>z)").parse(), Ok(Ast::Group(AstGroup {
            span: span(0..8),
            kind: AstGroupKind::CaptureName(AstCaptureName {
                span: span(4..5),
                name: "a".to_string(),
            }),
            ast: Box::new(lit('z', 6)),
        })));
        assert_eq!(parser("(?P<abc>z)").parse(), Ok(Ast::Group(AstGroup {
            span: span(0..10),
            kind: AstGroupKind::CaptureName(AstCaptureName {
                span: span(4..7),
                name: "abc".to_string(),
            }),
            ast: Box::new(lit('z', 8)),
        })));

        assert_eq!(parser("(?P<").parse(), Err(AstError {
            span: span(4..4),
            kind: AstErrorKind::GroupNameUnexpectedEof,
        }));
        assert_eq!(parser("(?P<>z)").parse(), Err(AstError {
            span: span(4..4),
            kind: AstErrorKind::GroupNameEmpty,
        }));
        assert_eq!(parser("(?P<a").parse(), Err(AstError {
            span: span(5..5),
            kind: AstErrorKind::GroupNameUnexpectedEof,
        }));
        assert_eq!(parser("(?P<ab").parse(), Err(AstError {
            span: span(6..6),
            kind: AstErrorKind::GroupNameUnexpectedEof,
        }));
        assert_eq!(parser("(?P<0a").parse(), Err(AstError {
            span: span(4..5),
            kind: AstErrorKind::GroupNameInvalid { c: '0' },
        }));
        assert_eq!(parser("(?P<~").parse(), Err(AstError {
            span: span(4..5),
            kind: AstErrorKind::GroupNameInvalid { c: '~' },
        }));
        assert_eq!(parser("(?P<abc~").parse(), Err(AstError {
            span: span(7..8),
            kind: AstErrorKind::GroupNameInvalid { c: '~' },
        }));
    }

    #[test]
    fn parse_flags() {
        assert_eq!(parser("i:").parse_flags(), Ok(AstFlags {
            span: span(0..1),
            items: vec![AstFlagsItem {
                span: span(0..1),
                kind: AstFlagsItemKind::Flag(AstFlag::CaseInsensitive),
            }],
        }));
        assert_eq!(parser("i)").parse_flags(), Ok(AstFlags {
            span: span(0..1),
            items: vec![AstFlagsItem {
                span: span(0..1),
                kind: AstFlagsItemKind::Flag(AstFlag::CaseInsensitive),
            }],
        }));

        assert_eq!(parser("isU:").parse_flags(), Ok(AstFlags {
            span: span(0..3),
            items: vec![
                AstFlagsItem {
                    span: span(0..1),
                    kind: AstFlagsItemKind::Flag(AstFlag::CaseInsensitive),
                },
                AstFlagsItem {
                    span: span(1..2),
                    kind: AstFlagsItemKind::Flag(AstFlag::DotMatchesNewLine),
                },
                AstFlagsItem {
                    span: span(2..3),
                    kind: AstFlagsItemKind::Flag(AstFlag::SwapGreed),
                },
            ],
        }));

        assert_eq!(parser("-isU:").parse_flags(), Ok(AstFlags {
            span: span(0..4),
            items: vec![
                AstFlagsItem {
                    span: span(0..1),
                    kind: AstFlagsItemKind::Negation,
                },
                AstFlagsItem {
                    span: span(1..2),
                    kind: AstFlagsItemKind::Flag(AstFlag::CaseInsensitive),
                },
                AstFlagsItem {
                    span: span(2..3),
                    kind: AstFlagsItemKind::Flag(AstFlag::DotMatchesNewLine),
                },
                AstFlagsItem {
                    span: span(3..4),
                    kind: AstFlagsItemKind::Flag(AstFlag::SwapGreed),
                },
            ],
        }));
        assert_eq!(parser("i-sU:").parse_flags(), Ok(AstFlags {
            span: span(0..4),
            items: vec![
                AstFlagsItem {
                    span: span(0..1),
                    kind: AstFlagsItemKind::Flag(AstFlag::CaseInsensitive),
                },
                AstFlagsItem {
                    span: span(1..2),
                    kind: AstFlagsItemKind::Negation,
                },
                AstFlagsItem {
                    span: span(2..3),
                    kind: AstFlagsItemKind::Flag(AstFlag::DotMatchesNewLine),
                },
                AstFlagsItem {
                    span: span(3..4),
                    kind: AstFlagsItemKind::Flag(AstFlag::SwapGreed),
                },
            ],
        }));

        assert_eq!(parser("isU").parse_flags(), Err(AstError {
            span: span(3..3),
            kind: AstErrorKind::FlagUnexpectedEof,
        }));
        assert_eq!(parser("isUa:").parse_flags(), Err(AstError {
            span: span(3..4),
            kind: AstErrorKind::FlagUnrecognized { flag: 'a' },
        }));
        assert_eq!(parser("isUi:").parse_flags(), Err(AstError {
            span: span(3..4),
            kind: AstErrorKind::FlagDuplicate {
                flag: 'i',
                original: span(0..1),
            },
        }));
        assert_eq!(parser("i-sU-i:").parse_flags(), Err(AstError {
            span: span(4..5),
            kind: AstErrorKind::FlagRepeatedNegation {
                original: span(1..2),
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
            span: span(0..1),
            kind: AstErrorKind::FlagUnrecognized { flag: 'a' },
        }));
        assert_eq!(parser("☃").parse_flag(), Err(AstError {
            span: span_with(0, "☃"),
            kind: AstErrorKind::FlagUnrecognized { flag: '☃' },
        }));
    }

    #[test]
    fn parse_primitive_non_escape() {
        assert_eq!(
            parser(r".").parse_primitive(),
            Ok(Primitive::Dot(span(0..1))));
        assert_eq!(
            parser(r"^").parse_primitive(),
            Ok(Primitive::Assertion(AstAssertion {
                span: span(0..1),
                kind: AstAssertionKind::StartLine,
            })));
        assert_eq!(
            parser(r"$").parse_primitive(),
            Ok(Primitive::Assertion(AstAssertion {
                span: span(0..1),
                kind: AstAssertionKind::EndLine,
            })));

        assert_eq!(
            parser(r"a").parse_primitive(),
            Ok(Primitive::Literal(AstLiteral {
                span: span(0..1),
                kind: AstLiteralKind::Verbatim,
                c: 'a',
            })));
        assert_eq!(
            parser(r"|").parse_primitive(),
            Ok(Primitive::Literal(AstLiteral {
                span: span(0..1),
                kind: AstLiteralKind::Verbatim,
                c: '|',
            })));
        assert_eq!(
            parser(r"☃").parse_primitive(),
            Ok(Primitive::Literal(AstLiteral {
                span: span_with(0, "☃"),
                kind: AstLiteralKind::Verbatim,
                c: '☃',
            })));
    }

    #[test]
    fn parse_escape() {
        assert_eq!(
            parser(r"\|").parse_primitive(),
            Ok(Primitive::Literal(AstLiteral {
                span: span(0..2),
                kind: AstLiteralKind::Punctuation,
                c: '|',
            })));
        let specials = &[
            (r"\a", '\x07'), (r"\f", '\x0C'), (r"\t", '\t'),
            (r"\n", '\n'), (r"\r", '\r'), (r"\v", '\x0B'),
        ];
        for &(pat, c) in specials {
            assert_eq!(
                parser(pat).parse_primitive(),
                Ok(Primitive::Literal(AstLiteral {
                    span: span(0..2),
                    kind: AstLiteralKind::Special,
                    c: c,
                })));
        }
        assert_eq!(
            parser(r"\A").parse_primitive(),
            Ok(Primitive::Assertion(AstAssertion {
                span: span(0..2),
                kind: AstAssertionKind::StartText,
            })));
        assert_eq!(
            parser(r"\z").parse_primitive(),
            Ok(Primitive::Assertion(AstAssertion {
                span: span(0..2),
                kind: AstAssertionKind::EndText,
            })));
        assert_eq!(
            parser(r"\b").parse_primitive(),
            Ok(Primitive::Assertion(AstAssertion {
                span: span(0..2),
                kind: AstAssertionKind::WordBoundary,
            })));
        assert_eq!(
            parser(r"\B").parse_primitive(),
            Ok(Primitive::Assertion(AstAssertion {
                span: span(0..2),
                kind: AstAssertionKind::NotWordBoundary,
            })));

        assert_eq!(parser(r"\").parse_escape(), Err(AstError {
            span: span(0..1),
            kind: AstErrorKind::EscapeUnexpectedEof,
        }));
        assert_eq!(parser(r"\y").parse_escape(), Err(AstError {
            span: span(0..2),
            kind: AstErrorKind::EscapeUnrecognized { c: 'y' },
        }));
    }

    #[test]
    fn parse_octal() {
        for i in 0..511 {
            let pat = format!(r"\{:o}", i);
            assert_eq!(
                parser(&pat).parse_escape(),
                Ok(Primitive::Literal(AstLiteral {
                    span: span(0..pat.len()),
                    kind: AstLiteralKind::Octal,
                    c: ::std::char::from_u32(i).unwrap(),
                })));
        }
        assert_eq!(
            parser(r"\778").parse_escape(),
            Ok(Primitive::Literal(AstLiteral {
                span: span(0..3),
                kind: AstLiteralKind::Octal,
                c: '?',
            })));
        assert_eq!(
            parser(r"\7777").parse_escape(),
            Ok(Primitive::Literal(AstLiteral {
                span: span(0..4),
                kind: AstLiteralKind::Octal,
                c: '\u{01FF}',
            })));
        assert_eq!(
            parser(r"\778").parse(),
            Ok(Ast::Concat(AstConcat {
                span: span(0..4),
                asts: vec![
                    Ast::Literal(AstLiteral {
                        span: span(0..3),
                        kind: AstLiteralKind::Octal,
                        c: '?',
                    }),
                    Ast::Literal(AstLiteral {
                        span: span(3..4),
                        kind: AstLiteralKind::Verbatim,
                        c: '8',
                    }),
                ],
            })));
        assert_eq!(
            parser(r"\7777").parse(),
            Ok(Ast::Concat(AstConcat {
                span: span(0..5),
                asts: vec![
                    Ast::Literal(AstLiteral {
                        span: span(0..4),
                        kind: AstLiteralKind::Octal,
                        c: '\u{01FF}',
                    }),
                    Ast::Literal(AstLiteral {
                        span: span(4..5),
                        kind: AstLiteralKind::Verbatim,
                        c: '7',
                    }),
                ],
            })));

        assert_eq!(parser(r"\8").parse_escape(), Err(AstError {
            span: span(0..2),
            kind: AstErrorKind::EscapeUnrecognized { c: '8' },
        }));
    }

    #[test]
    fn parse_hex_two() {
        for i in 0..256 {
            let pat = format!(r"\x{:02x}", i);
            assert_eq!(
                parser(&pat).parse_escape(),
                Ok(Primitive::Literal(AstLiteral {
                    span: span(0..pat.len()),
                    kind: AstLiteralKind::Hex,
                    c: ::std::char::from_u32(i).unwrap(),
                })));
        }
        for i in 0..256 {
            let pat = format!(r"\x{:02X}", i);
            assert_eq!(
                parser(&pat).parse_escape(),
                Ok(Primitive::Literal(AstLiteral {
                    span: span(0..pat.len()),
                    kind: AstLiteralKind::Hex,
                    c: ::std::char::from_u32(i).unwrap(),
                })));
        }

        assert_eq!(parser(r"\xF").parse_escape(), Err(AstError {
            span: span(3..3),
            kind: AstErrorKind::EscapeUnexpectedEof,
        }));
        assert_eq!(parser(r"\xFG").parse_escape(), Err(AstError {
            span: span(3..4),
            kind: AstErrorKind::EscapeHexInvalidDigit { c: 'G' },
        }));
    }

    #[test]
    fn parse_hex_brace() {
        assert_eq!(
            parser(r"\x{26c4}").parse_escape(),
            Ok(Primitive::Literal(AstLiteral {
                span: span(0..8),
                kind: AstLiteralKind::Unicode,
                c: '⛄',
            })));
        assert_eq!(
            parser(r"\x{26C4}").parse_escape(),
            Ok(Primitive::Literal(AstLiteral {
                span: span(0..8),
                kind: AstLiteralKind::Unicode,
                c: '⛄',
            })));
        assert_eq!(
            parser(r"\x{10fFfF}").parse_escape(),
            Ok(Primitive::Literal(AstLiteral {
                span: span(0..10),
                kind: AstLiteralKind::Unicode,
                c: '\u{10FFFF}',
            })));

        assert_eq!(parser(r"\x").parse_escape(), Err(AstError {
            span: span(2..2),
            kind: AstErrorKind::EscapeUnexpectedEof,
        }));
        assert_eq!(parser(r"\x{").parse_escape(), Err(AstError {
            span: span(2..3),
            kind: AstErrorKind::EscapeUnexpectedEof,
        }));
        assert_eq!(parser(r"\x{FF").parse_escape(), Err(AstError {
            span: span(2..5),
            kind: AstErrorKind::EscapeUnexpectedEof,
        }));
        assert_eq!(parser(r"\x{}").parse_escape(), Err(AstError {
            span: span(2..4),
            kind: AstErrorKind::EscapeHexEmpty,
        }));
        assert_eq!(parser(r"\x{FGF}").parse_escape(), Err(AstError {
            span: span(4..5),
            kind: AstErrorKind::EscapeHexInvalidDigit { c: 'G' },
        }));
        assert_eq!(parser(r"\x{FFFFFF}").parse_escape(), Err(AstError {
            span: span(3..9),
            kind: AstErrorKind::EscapeHexInvalid,
        }));
        assert_eq!(parser(r"\x{D800}").parse_escape(), Err(AstError {
            span: span(3..7),
            kind: AstErrorKind::EscapeHexInvalid,
        }));
        assert_eq!(parser(r"\x{FFFFFFFFF}").parse_escape(), Err(AstError {
            span: span(3..12),
            kind: AstErrorKind::EscapeHexInvalid,
        }));
    }

    #[test]
    fn parse_unicode_class() {
        assert_eq!(
            parser(r"\pN").parse_escape(),
            Ok(Primitive::Unicode(AstClassUnicode {
                span: span(0..3),
                kind: AstClassUnicodeKind::OneLetter,
                negated: false,
                name: "N".to_string(),
            })));
        assert_eq!(
            parser(r"\PN").parse_escape(),
            Ok(Primitive::Unicode(AstClassUnicode {
                span: span(0..3),
                kind: AstClassUnicodeKind::OneLetter,
                negated: true,
                name: "N".to_string(),
            })));
        assert_eq!(
            parser(r"\p{N}").parse_escape(),
            Ok(Primitive::Unicode(AstClassUnicode {
                span: span(0..5),
                kind: AstClassUnicodeKind::Bracketed,
                negated: false,
                name: "N".to_string(),
            })));
        assert_eq!(
            parser(r"\P{N}").parse_escape(),
            Ok(Primitive::Unicode(AstClassUnicode {
                span: span(0..5),
                kind: AstClassUnicodeKind::Bracketed,
                negated: true,
                name: "N".to_string(),
            })));
        assert_eq!(
            parser(r"\p{Greek}").parse_escape(),
            Ok(Primitive::Unicode(AstClassUnicode {
                span: span(0..9),
                kind: AstClassUnicodeKind::Bracketed,
                negated: false,
                name: "Greek".to_string(),
            })));

        assert_eq!(parser(r"\p").parse_escape(), Err(AstError {
            span: span(2..2),
            kind: AstErrorKind::EscapeUnexpectedEof,
        }));
        assert_eq!(parser(r"\p{").parse_escape(), Err(AstError {
            span: span(3..3),
            kind: AstErrorKind::EscapeUnexpectedEof,
        }));
        assert_eq!(parser(r"\p{N").parse_escape(), Err(AstError {
            span: span(4..4),
            kind: AstErrorKind::EscapeUnexpectedEof,
        }));
        assert_eq!(parser(r"\p{Greek").parse_escape(), Err(AstError {
            span: span(8..8),
            kind: AstErrorKind::EscapeUnexpectedEof,
        }));

        assert_eq!(
            parser(r"\pNz").parse(),
            Ok(Ast::Concat(AstConcat {
                span: span(0..4),
                asts: vec![
                    Ast::Class(AstClass::Unicode(AstClassUnicode {
                        span: span(0..3),
                        kind: AstClassUnicodeKind::OneLetter,
                        negated: false,
                        name: "N".to_string(),
                    })),
                    Ast::Literal(AstLiteral {
                        span: span(3..4),
                        kind: AstLiteralKind::Verbatim,
                        c: 'z',
                    }),
                ],
            })));
        assert_eq!(
            parser(r"\p{Greek}z").parse(),
            Ok(Ast::Concat(AstConcat {
                span: span(0..10),
                asts: vec![
                    Ast::Class(AstClass::Unicode(AstClassUnicode {
                        span: span(0..9),
                        kind: AstClassUnicodeKind::Bracketed,
                        negated: false,
                        name: "Greek".to_string(),
                    })),
                    Ast::Literal(AstLiteral {
                        span: span(9..10),
                        kind: AstLiteralKind::Verbatim,
                        c: 'z',
                    }),
                ],
            })));
    }

    #[test]
    fn parse_perl_class() {
        assert_eq!(
            parser(r"\d").parse_escape(),
            Ok(Primitive::Perl(AstClassPerl {
                span: span(0..2),
                kind: AstClassPerlKind::Digit,
                negated: false,
            })));
        assert_eq!(
            parser(r"\D").parse_escape(),
            Ok(Primitive::Perl(AstClassPerl {
                span: span(0..2),
                kind: AstClassPerlKind::Digit,
                negated: true,
            })));
        assert_eq!(
            parser(r"\s").parse_escape(),
            Ok(Primitive::Perl(AstClassPerl {
                span: span(0..2),
                kind: AstClassPerlKind::Space,
                negated: false,
            })));
        assert_eq!(
            parser(r"\S").parse_escape(),
            Ok(Primitive::Perl(AstClassPerl {
                span: span(0..2),
                kind: AstClassPerlKind::Space,
                negated: true,
            })));
        assert_eq!(
            parser(r"\w").parse_escape(),
            Ok(Primitive::Perl(AstClassPerl {
                span: span(0..2),
                kind: AstClassPerlKind::Word,
                negated: false,
            })));
        assert_eq!(
            parser(r"\W").parse_escape(),
            Ok(Primitive::Perl(AstClassPerl {
                span: span(0..2),
                kind: AstClassPerlKind::Word,
                negated: true,
            })));

        assert_eq!(
            parser(r"\d").parse(),
            Ok(Ast::Class(AstClass::Perl(AstClassPerl {
                span: span(0..2),
                kind: AstClassPerlKind::Digit,
                negated: false,
            }))));
        assert_eq!(
            parser(r"\dz").parse(),
            Ok(Ast::Concat(AstConcat {
                span: span(0..3),
                asts: vec![
                    Ast::Class(AstClass::Perl(AstClassPerl {
                        span: span(0..2),
                        kind: AstClassPerlKind::Digit,
                        negated: false,
                    })),
                    Ast::Literal(AstLiteral {
                        span: span(2..3),
                        kind: AstLiteralKind::Verbatim,
                        c: 'z',
                    }),
                ],
            })));
    }
}
