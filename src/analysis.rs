//! Well-formedness checking (semantic analysis) of dice expressions.
//!
//! We need to make sure:
//! - All symbols are defined when used.
//! - Symbols do not conflict.
//! - Keep-highest / keep-lowest are always valid
//! - Division never divides by zero
//!
//!
//! TODO: Conditionals are nonlinear, so we can't generate min/max.
//! We have to just handle the whole path.

use std::{collections::HashSet, str::FromStr};

use crate::{
    Error,
    parse::RawExpression,
    symbolic::{Constant, Die, ExpressionTree, ExpressionWrapper, Symbol},
};

/// An expression tree that is possibly closed (has no unbound symbols).
#[derive(Clone)]
pub enum MaybeClosed {
    Closed(Box<ExpressionTree<MaybeClosed>>),
    Open(Box<ExpressionTree<MaybeClosed>>),
}

impl ExpressionWrapper for MaybeClosed {
    fn inner(&self) -> &ExpressionTree<Self> {
        match self {
            MaybeClosed::Closed(maybe_closed) => maybe_closed.as_ref(),
            MaybeClosed::Open(maybe_closed) => maybe_closed.as_ref(),
        }
    }
}

impl TryFrom<RawExpression> for MaybeClosed {
    type Error = Error;

    fn try_from(value: RawExpression) -> Result<Self, Self::Error> {
        todo!()
    }
}

/// An expression which is closed: no unbound symbols.
//
// Note that this is not an ExpressionTree<Closed> because the inner expressions may contain
// symbols / bindings.
pub struct Closed(ExpressionTree<MaybeClosed>);

impl MaybeClosed {
    /// Return either a Closed expression tree, or a list of the unbound symbols.
    pub fn closed(&self) -> Result<Closed, HashSet<Symbol>> {
        match self {
            MaybeClosed::Closed(expression_tree) => Ok(Closed(expression_tree.as_ref().clone())),
            MaybeClosed::Open(expression_tree) => {
                Self::closed_under(&AvailableBinding::Root, expression_tree.as_ref())?;
                Ok(Closed(expression_tree.as_ref().clone()))
            }
        }
    }

    fn closed_under(
        bindings: &AvailableBinding<MaybeClosed>,
        tree: &ExpressionTree<MaybeClosed>,
    ) -> Result<(), HashSet<Symbol>> {
        match tree {
            ExpressionTree::Modifier(_) => Ok(()),
            ExpressionTree::Die(_) => Ok(()),
            ExpressionTree::Symbol(symbol) => {
                Err([symbol.clone()].into_iter().collect::<HashSet<_>>())
            }
            ExpressionTree::Negated(n) => {
                Self::closed_under(bindings, n.inner())?;
                Ok(())
            }
            ExpressionTree::Repeated {
                count,
                value,
                ranker: _,
            } => {
                Self::closed_under(bindings, count.inner())?;
                Self::closed_under(bindings, value.inner())?;
                Ok(())
            }
            ExpressionTree::Product(a, b) => {
                Self::closed_under(bindings, a.inner())?;
                Self::closed_under(bindings, b.inner())?;
                Ok(())
            }
            ExpressionTree::Sum(items) => {
                for item in items {
                    Self::closed_under(bindings, item.inner())?;
                }
                Ok(())
            }
            ExpressionTree::Floor(a, b) => {
                Self::closed_under(bindings, a.inner())?;
                Self::closed_under(bindings, b.inner())?;
                Ok(())
            }
            ExpressionTree::Comparison { a, b, op: _ } => {
                Self::closed_under(bindings, a.inner())?;
                Self::closed_under(bindings, b.inner())?;
                Ok(())
            }

            ExpressionTree::Binding {
                symbol,
                value,
                tail,
            } => {
                Self::closed_under(bindings, value.inner())?;
                Self::closed_under(
                    &AvailableBinding::Chain {
                        defined: symbol,
                        definition: value,
                        prev: bindings,
                    },
                    tail.inner(),
                )?;
                Ok(())
            }
        }
    }
}

/// Linked list (on the stack) of current symbol bindings.
#[derive(Copy, Clone)]
enum AvailableBinding<'a, T: ExpressionWrapper> {
    Root,
    Chain {
        defined: &'a Symbol,
        definition: &'a T,
        prev: &'a AvailableBinding<'a, T>,
    },
}

impl<T: ExpressionWrapper> AvailableBinding<'_, T> {
    /// Search the stack of bindings for the provided symbol.
    fn search(&self, needle: &Symbol) -> Option<&T> {
        let mut current: &AvailableBinding<T> = self;
        while let AvailableBinding::Chain {
            defined,
            prev,
            definition,
        } = current
        {
            if *defined == needle {
                return Some(definition);
            } else {
                current = *prev;
            }
        }
        None
    }
}

//#[cfg(test)]
//mod tests {
//    use super::*;
//
//    #[test]
//    fn undefined_reference() {
//        let v: RawExpression = "[ABC: 1d20] BCD".parse().unwrap();
//        let e = std::convert::TryInto::<WellFormed>::try_into(v).unwrap_err();
//        let e_target: Symbol = "BCD".parse().unwrap();
//        match e {
//            crate::Error::SymbolUndefined(sym) if sym == e_target => (),
//            x => panic!("unexpected error: {x}"),
//        }
//    }
//
//    #[test]
//    fn redefined_reference() {
//        let v: RawExpression = "[ABC: 1d20] [ABC:2d10] ABC + ABC".parse().unwrap();
//        let e = std::convert::TryInto::<WellFormed>::try_into(v).unwrap_err();
//        let e_target = "ABC".parse().unwrap();
//        assert!(matches!(e, crate::Error::SymbolRedefined(sym) if sym == e_target));
//    }
//
//    #[test]
//    fn undefined_contextural() {
//        let v: RawExpression = "2([ATK: 1d20] (ATK + 1 > 10) * 10) + ATK".parse().unwrap();
//        let e = std::convert::TryInto::<WellFormed>::try_into(v).unwrap_err();
//        let e_target = "ATK".parse().unwrap();
//        assert!(matches!(e, crate::Error::SymbolUndefined(sym) if sym == e_target));
//    }
//
//    #[test]
//    fn keep_enough_high() {
//        let v: RawExpression = "3d20kh4".parse().unwrap();
//        let e = std::convert::TryInto::<WellFormed>::try_into(v).unwrap_err();
//        assert!(matches!(e, crate::Error::KeepTooFew(_, _)));
//    }
//
//    #[test]
//    fn keep_enough_low() {
//        let v: RawExpression = "3d20kl4".parse().unwrap();
//        let e = std::convert::TryInto::<WellFormed>::try_into(v).unwrap_err();
//        assert!(matches!(e, crate::Error::KeepTooFew(_, _)));
//    }
//
//    #[test]
//    fn no_zero_in_denominator_range() {
//        let v: RawExpression = "10 / (1d20 - 10)".parse().unwrap();
//        let e = std::convert::TryInto::<WellFormed>::try_into(v).unwrap_err();
//        assert!(matches!(e, crate::Error::DivideByZero(_)));
//    }
//
//    #[test]
//    fn no_zero_faced_dice() {
//        let v: RawExpression = "d0".parse().unwrap();
//        let e = std::convert::TryInto::<WellFormed>::try_into(v).unwrap_err();
//        assert!(matches!(e, crate::Error::ZeroFacedDie()));
//    }
//
//    #[test]
//    fn minimum() {
//        for (i, (e, min)) in [
//            ("20 / 2", 10),
//            ("1d20 / 1d10", 0),
//            ("-1d20", -20),
//            ("1d20", 1),
//            ("-1d20 / 1d20", -20),
//            ("1d20 / -1d20", -20),
//            ("[ATK: 1d20] ATK+3", 4),
//            ("1d2 * 1d2", 1),
//            ("1d2 < 2", 0),
//            ("[ATK: 1d20] -ATK", -20),
//            ("[ATK: -1d20] -ATK", 1),
//            ("2d10", 2),
//        ]
//        .into_iter()
//        .enumerate()
//        {
//            let e: WellFormed = e.parse().unwrap();
//            assert_eq!(e.minimum(), min, "case {i} for expression {e}");
//        }
//    }
//    #[test]
//    fn maximum() {
//        for (i, (e, max)) in [
//            ("20 / 2", 10),
//            ("1d20 / 1d10", 20),
//            ("-1d20", -1),
//            ("1d20", 20),
//            ("-1d20 / 1d20", 0),
//            ("1d20 / -1d20", 0),
//            ("[ATK: 1d20] ATK+3", 23),
//            ("1d2 * 1d2", 4),
//            ("1d2 > 1", 1),
//            ("[ATK: 1d20] -ATK", -1),
//            ("[ATK: -1d20] -ATK", 20),
//            ("2d10", 20),
//        ]
//        .into_iter()
//        .enumerate()
//        {
//            let e: WellFormed = e.parse().unwrap();
//            assert_eq!(e.maximum(), max, "case {i} for expression {e}");
//        }
//    }
//
//    #[test]
//    #[ignore = "TODO: Incorrect; breaks linearity assumption"]
//    fn attack_rolls() {
//        // Complicated ones: Eldritch Blast, with Agonizing Blast, including critical effects.
//        for (i, (e, max)) in [
//            ("[AC: 16] [CHA: +5] [ATK: 1d20] (ATK = 20) * (2d10 + CHA) + (ATK < 20) * (ATK > 1) * (ATK + CHA >= AC) * (1d10 + CHA)", 25),
//            ("2([AC: 16] [ATK: 1d20] [CHA: +5] (ATK = 20) * (2d10 + CHA) + (ATK < 20) * (ATK > 1) * (ATK + CHA >= AC) * (1d10 + CHA))", 50),
//            ("[AC: 16] [CHA: +5] 2([ATK: 1d20] (ATK = 20) * (2d10 + CHA) + (ATK < 20) * (ATK > 1) * (ATK + CHA >= AC) * (1d10 + CHA))", 50),
//        ].into_iter().enumerate() {
//            let e : WellFormed = e.parse().unwrap();
//            assert_eq!(e.minimum(), 0); // critical miss
//            assert_eq!(e.maximum(), max); // critical miss
//        }
//    }
//}
