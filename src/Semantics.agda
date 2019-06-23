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

