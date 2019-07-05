module Semantics where
-- This module corresponds to the Section 2.2 of the book

open import Data.Maybe
open import Data.Nat
open import Data.Bool
open import Data.List
open import Syntax

-- Define the store (environment) by a function

-- TODO : define Store with a list and get function with nil as default
-- return value
Store = Wvar → Maybe Wdata

-- we need bool equality on Wvar
_==_ : Wvar → Wvar → Bool
(var n₁) == (var n₂) = n₁ ≡ᵇ n₂

-- and bool equality between Wdata
_≡ᵈ_ : Wdata → Wdata → Bool
nil       ≡ᵈ nil       = true
(d₁ • d₂) ≡ᵈ (d₃ • d₄) = (d₁ ≡ᵈ d₃) ∧ (d₂ ≡ᵈ d₄)
_         ≡ᵈ _         = false

-- the empty store
stempty : Store
stempty _ = nothing

stupdate : Wvar → Wdata → Store → Store
stupdate v₁ d f v₂ with v₁ == v₂
... | true  = just d
... | false = f v₂

stremove : Wvar → Store → Store
stremove v₁ f v₂ with v₁ == v₂
... | true  = nothing
... | false = f v₂

-- we need to get the set of all the variables of a While program
varsBlock : Wcommand → List Wvar
varsBlock (v ≔ _)         = [ v ]
varsBlock (b₁ %% b₂)      = varsBlock b₁ ++ varsBlock b₂
varsBlock (while _ do: b) = varsBlock b

-- Get the list of Wvar in a WProgram with input in first var and
-- output in second element of the list
nodupVarAux : List Wvar → List Wvar → List Wvar
nodupVarAux acc [] = acc
nodupVarAux acc (x ∷ xs) with any (λ v → x == v) acc
... | true  = nodupVarAux acc xs
... | false = nodupVarAux (x ∷ acc) xs 

nodupVar : List Wvar → List Wvar
nodupVar l = nodupVarAux [] l

varsAux : WProgram → List Wvar
varsAux (record { readInput = r ; blockProg = b ; writeOutput = o }) = r ∷ o ∷ (varsBlock b)

vars : WProgram → List Wvar
vars r = nodupVar (varsAux r)

-- initialiaze store for a program and an input
initStore : WProgram → Wdata → Store
initStore pg d = stupdate (WProgram.readInput pg) d (foldr (λ v → stupdate v nil) stempty (vars pg))

-- evaluate an expression in regard to a store
evalExp : Wexp → Store → Wdata
evalExp (xvar v) st with st v
... | nothing = nil
... | just e  = e
evalExp atom _                 = nil
evalExp (cons e₁ e₂) st        = (evalExp e₁ st) • (evalExp e₂ st)
evalExp (tail (cons e₁ e₂)) st = evalExp e₂ st
evalExp (tail _) _             = nil
evalExp (head (cons e₁ e₂)) st = evalExp e₁ st
evalExp (head _) _             = nil
evalExp (isEq e₁ e₂) st with (evalExp e₁ st) ≡ᵈ (evalExp e₂ st)
... | true = nil • nil
... | false = nil

-- Define intermediary representation of Wcommands
data InterCom : Set where
  assign    : Wvar → Wexp → InterCom
  whilecond : Wexp → InterCom
  whileend  : InterCom

-- organize evaluation with an instruction pointer
record WPointCom : Set where
  constructor _,_
  field
    pointer : ℕ
    command : InterCom

ProgBlock = List WPointCom

buildInterProg : Wcommand → List InterCom
buildInterProg (x ≔ y)         = [ (assign x y) ]
buildInterProg (c₁ %% c₂)      = (buildInterProg c₁) ++ (buildInterProg c₂)
buildInterProg (while e do: c) = (whilecond e) ∷ (buildInterProg c) ++ [ whileend ]

numProg : ℕ → List InterCom → ProgBlock
numProg _ []       = []
numProg n (x ∷ xs) = (n , x) ∷ numProg (suc n) xs
buildProgBlock : Wcommand → ProgBlock
buildProgBlock c = numProg zero (buildInterProg c)

record DoubleStack : Set where
  field
    stack1 : ProgBlock
    stack2 : ProgBlock

record Wenv : Set where
  field
    st      : Store
    cpt     : ℕ
    stack   : List ℕ
    cmds    : DoubleStack 
    output  : Wvar

prepProg : WProgram → Wdata → Wenv
prepProg p d = record { st      = initStore p d ;
                        cpt     = 0 ;
                        stack   = [] ;
                        cmds    = record { stack1 = [] ; stack2 = buildProgBlock (WProgram.blockProg p) } ;
                        output  = WProgram.writeOutput p }
