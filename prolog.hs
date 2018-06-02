{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE TemplateHaskell            #-}

module Main where

#if MIN_VERSION_base(4,11,0)
import Prelude hiding ( (<>) )
#endif

import Control.Lens
import Control.Monad
import Data.Char
import Data.Data
import Data.Map as Map
import Data.Maybe
import Data.Semigroup ( Semigroup )
import Data.Set.Lens as Set
import Distribution.Compat.ReadP as ReadP
import Distribution.Text
import Text.PrettyPrint as PP

-- * Lexical Structure, Parsing, and Pretty-Printing

type Atom = String
type VariableName = Atom
type FunctorName = Atom

data Term = Constant Atom
          | Variable VariableName
          | Structure FunctorName [Term]
  deriving (Show, Eq, Data, Typeable)

instance Plated Term where

makePrisms ''Term

instance Text Term where
  disp (Constant a) = text a
  disp (Variable a) = text a
  disp (Structure a b) = text a <> parens (hcat (punctuate comma (disp <$> b)))
  parse = choice [ token (ReadP.char '[') >> token (ReadP.char ']') >> return (Constant "[]")
                 , Structure <$> parseFunctor <*> pBracket (sepBy parse pComma)
                 , Constant <$> parseFunctor
                 , Variable <$> token (munch1 (\c -> isUpper c || isDigit c || c == '_'))
                 ]
    where parseFunctor = token (operator <++ name)
          operator     = token (munch1 (`elem` "+-*/<=>'\\:.?@#$^~"))
          name         = (:) <$> satisfy isLower <*> munch (\c -> isAlphaNum c || c == '_')
          pComma       = token (ReadP.char ',')
          pBracket     = between (token (ReadP.char '(')) (token (ReadP.char ')'))

pTerm :: String -> Term
pTerm s = fromMaybe (error ("no valid Prolog Term: " ++ s)) (simpleParse s)

token :: ReadP r a -> ReadP r a
token p = skipSpaces >> p

-- * Substitutions

newtype Substitution = Substitution (Map VariableName Term)
  deriving (Eq, Show, Semigroup, Monoid)

instance Text Substitution where
  disp (Substitution s) = braces (fsep (punctuate comma [ text vn <> PP.char '/' <> disp t | (vn, t) <- Map.toList s ]))
  parse = error "no parser defined for substitutions"

apply :: Substitution -> Term -> Term
apply (Substitution s) = transform (\case { Variable a -> Map.findWithDefault (Variable a) a s; t -> t })

compose :: Substitution -> Substitution -> Substitution
compose (Substitution l) (Substitution r) = Substitution (Map.union l (Map.map (apply (Substitution l)) r))

restrict :: Substitution -> Term -> Substitution
restrict (Substitution s) t = Substitution (Map.filterWithKey (\k _ -> k `elem` names) s)
  where names = setOf (plate . _Variable) t

subst :: [(VariableName, Term)] -> Maybe Substitution
subst = return . Substitution . Map.fromList

-- * Unification

unify :: Term -> Term -> Maybe Substitution
unify (Variable a)     (Variable b)     | a == b        = subst []
unify a                (Variable b)     | b `freeIn` a  = subst [(b,a)]
unify (Variable a)     b                | a `freeIn` b  = subst [(a,b)]
unify (Constant a)     (Constant b)                     = if a == b then subst [] else mzero
unify (Structure a as) (Structure b bs)                 = if a == b && length as == length bs
                                                             then unifyStructure as bs
                                                             else mzero
unify _ _                                               = mzero

unifyStructure :: [Term] -> [Term] -> Maybe Substitution
unifyStructure []     []     = subst []
unifyStructure []     _      = fail "logic error"
unifyStructure _      []     = fail "logic error"
unifyStructure (a:as) (b:bs) = do s  <- unify a b
                                  s' <- unifyStructure (apply s <$> as) (apply s <$> bs)
                                  return (s' `compose` s)

occursIn :: VariableName -> Term -> Bool
occursIn a = elem a . toListOf (plate . _Variable)

freeIn :: VariableName -> Term -> Bool
freeIn a = not . occursIn a

-- * Finding Proofs

data Rule = Rule Term [Term]
  deriving (Show, Data, Typeable)

instance Each Rule Rule Term Term where
  each f (Rule r rs) = Rule <$> f r <*> traverse f rs

instance Text Rule where
  disp (Rule a []) = disp a <+> PP.char '.'
  disp (Rule a b)  = disp a <+> text ":-" <+> hcat (punctuate comma (disp <$> b)) <+> PP.char '.'
  parse = do lhs <- token parse
             rhs <- option [] $ do _ <- token (ReadP.string ":-")
                                   sepBy1 (token parse) (token (ReadP.char ','))
             _ <- token (ReadP.char '.')
             return (Rule lhs rhs)

splits :: [a] -> [([a], [a])]
splits as = [ Prelude.splitAt i as | i <- [0 .. length as - 1] ]

prove :: [Rule] -> [Term] -> [Substitution]
prove rules' terms' = prove' terms' mempty
  where
    rules = over (traverse . each . _Variable) ('#':) rules'

    prove' :: [Term] -> Substitution -> [Substitution]
    prove' []    sigma = [sigma]
    prove' terms sigma = [ sigma'
                         | (tPrefix,t:tSuffix) <- splits terms
                         , Rule r rs <- rules
                         , Just s <- [unify t r]
                         , s' <- [compose s sigma]
                         , sigma' <- prove' (tPrefix ++ (apply s' <$> rs) ++ tSuffix) (restrict s' t)
                         ]

-- disp <$> prove prog (pTerm <$> ["member(L, .(h, .(a, .(l, .(l, .(o, []))))))"])
-- disp <$> prove prog (pTerm <$> ["last(.(h, .(a, .(l, .(l, .(o, []))))), L)"])

prog :: [Rule]
prog = fromJust . simpleParse <$>
       [ "member(X, .(X, _)) ."
       , "member(X, .(_, XS)) :- member(X, XS) ."
       , "last(.(L,[]), L) ."
       , "last(.(_,LS), L) :- last(LS, L) ."
       ]

main :: IO ()
main = getContents >>= mapM_ (putStrLn . display) . prove prog . fmap pTerm . lines
