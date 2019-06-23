module Semantics where
-- This module conrrespond to the Section 2.2 of the book

-- could use :
-- open import Data.AVL.IndexedMap
open import Data.Maybe
open import Data.Nat
open import Data.Bool
open import Data.List
open import Syntax

-- Define the store (environment) by a function

Store = Wvar → Maybe Wdata

-- we need bool equality on Wvar
_==_ : Wvar → Wvar → Bool
(var n₁) == (var n₂) = n₁ ≡ᵇ n₂

-- and bool equality between Wdata
_≡ᵈ_ : Wdata → Wdata → Bool
nil       ≡ᵈ nil       = true
(d₁ • d₂) ≡ᵈ (d₃ • d₄) = (d₁ ≡ᵈ d₃) ∧ (d₂ ≡ᵈ d₄)
d₁        ≡ᵈ d₂        = false

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

-- Get the list of Wvar in a WProgram
nodupVar : List Wvar → List Wvar
nodupVar [] = []
nodupVar (x ∷ xs) with any (λ v → x == v) xs
... | true  = nodupVar xs
... | false = x ∷ (nodupVar xs)

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
  assign  : Wvar → Wexp → InterCom
  whilecond : Wexp → InterCom

-- organize evaluation with an instruction pointer
record WPointCom : Set where
  constructor _,_
  field
    pointer : ℕ
    command : InterCom

ProgBlock = List WPointCom


-- Pb: ugly def for sequence
numProgAux : ℕ → Wcommand → ProgBlock
numProgAux n (x ≔ y)    = [ (n , (assign x y)) ]
numProgAux n (c₁ %% c₂) = (numProgAux n c₁) ++ (numProgAux (n + (length (numProgAux n c₁))) c₂)
numProgAux n (while e do: c) = (n , (whilecond e)) ∷ (numProgAux (n + 1) c)

record Wenv : Set where
  field
    st : Store
    cpt : ℕ
    stack : List ℕ
    pg : ProgBlock

PrepProg : WProgram → Wdata → Wenv
PrepProg p d = record { st = initStore p d ; cpt = 0 ; stack = [] ; pg = numProgAux 0 (WProgram.blockProg p) }
