module Semantics where
-- This module corresponds to the Section 2.2 of the book

open import IntermediaryRepresentation
open import Syntax
open import Data.List
open import Data.Bool
open import Data.Nat
open import Relation.Binary.PropositionalEquality


-- Small Step Semantic for While Language As a Function
oneStepEval : Wenv → Wenv
-- assignement
oneStepEval (record { st     = s ;
                      stack  = l ;
                      cmds   = s₁ ∣ (cmd@(n , (assign x y)) ∷ s₂) ;
                      output = o }) = record { st     = stupdate x (evalExp y s) s ;
                                               stack  = l ;
                                               cmds   = (cmd ∷ s₁) ∣ s₂ ;
                                               output = o }
-- enter while loop                             
oneStepEval (record { st     = s ;
                      stack  = l ;
                      cmds   = s₁ ∣ (cmd@(n , whileBegin) ∷ s₂) ;
                      output = o }) = record { st     = s ;
                                               stack  = n ∷ l ;
                                               cmds   = (cmd ∷ s₁) ∣ s₂ ;
                                               output = o }
-- end of while loop                      
oneStepEval (record { st     = s ;
                      stack  = l@(x ∷ xs) ;
                      cmds   = d@(s₁ ∣ (cmd@(n , (whileEnd e)) ∷ s₂)) ;
                      output = o }) with evalExp e s ≡ᵈ nil
... | true  = record { st     = s ;
                       stack  = xs ;
                       cmds   = (cmd ∷ s₁) ∣ s₂ ;
                       output = o }
... | false = record { st     = s ;
                       stack  = l ;
                       cmds   = goBackTo x d ;
                       output = o }
-- end of pg -- do nothing
oneStepEval r = r

infix 4 _⟶_

-- Small Step Semenatic as Data Structure
data _⟶_ : Wenv → Wenv → Set where

  ε-assign : ∀ {s : Store} {l : List ℕ } {n : ℕ} {s₁ s₂ : ProgBlock} {y : Wexp} {x o : Wvar}
             → record { st     = s ;
                        stack  = l ;
                        cmds   = s₁ ∣ (n , (assign x y) ∷ s₂) ;
                        output = o }
             ⟶ -----------------------------------------------
             record { st     = stupdate x (evalExp y s) s ;
                      stack  = l ;
                      cmds   = ((n , (assign x y)) ∷ s₁) ∣ s₂ ;
                      output = o }

  ε-whileBegin : ∀ {s : Store} {l : List ℕ } {n : ℕ} {s₁ s₂ : ProgBlock} {o : Wvar}
                 → record { st     = s ;
                            stack  = l ;
                            cmds   = s₁ ∣ ((n , whileBegin) ∷ s₂) ;
                            output = o }
                 ⟶ -----------------------------------------------
                 record { st     = s ;
                          stack  = n ∷ l ;
                          cmds   = ((n , whileBegin) ∷ s₁) ∣ s₂ ;
                          output = o }
  
  ε-whileEndNil : ∀ {s : Store} {xs : List ℕ} {x n : ℕ} {e : Wexp} {s₁ s₂ : ProgBlock} {o : Wvar} {check : (evalExp e s ≡ᵈ nil) ≡ true}
                  → record { st     = s ;
                             stack  = x ∷ xs ;
                             cmds   = s₁ ∣ ((n , (whileEnd e)) ∷ s₂) ;
                             output = o }
                  ⟶ ------------------------------------------
                  record { st     = s ;
                           stack  = xs ;
                           cmds   = ((n , (whileEnd atom)) ∷ s₁) ∣ s₂ ;
                           output = o }
  ε-whileEndNotNil : ∀ {s : Store} {xs : List ℕ} {x n : ℕ} {e : Wexp} {s₁ s₂ : ProgBlock} {o : Wvar} {check : (evalExp e s ≡ᵈ nil) ≡ false}
                     → record { st     = s ;
                             stack  = xs ;
                             cmds   = s₁ ∣ ((n , (whileEnd e)) ∷ s₂) ;
                             output = o }
                  ⟶ ------------------------------------------
                  record { st     = s ;
                           stack  = x ∷ xs ;
                           cmds   = goBackTo x (s₁ ∣ ((n , (whileEnd e)) ∷ s₂)) ;
                           output = o }
