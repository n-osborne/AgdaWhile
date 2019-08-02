module Syntax where
-- this module formalises the syntax of the While language as it is
-- defined in Neil Jones, _Computability and Complexity_ p. 32

open import Data.Nat

-- The variable for the While language are identified by a ℕ
data Wvar : Set where
  var : ℕ → Wvar

-- The data of the While language is a binaty tree on the singleton
-- {nil}
data Wdata : Set where
  nil : Wdata
  _•_ : Wdata → Wdata → Wdata

-- Definition of the expressions of the While language
data Wexp : Set where
  xvar : Wvar → Wexp
  atom : Wexp
  cons : Wexp → Wexp → Wexp
  tail : Wexp → Wexp
  head : Wexp → Wexp
  isEq : Wexp → Wexp → Wexp

-- The While language has only three commands:
--   1. assignement
--   2. sequence
--   3. while loop
data Wcommand : Set where
  _≔_        : Wvar → Wexp → Wcommand
  _%%_       : Wcommand → Wcommand → Wcommand
  while_do:_ : Wexp → Wcommand → Wcommand

-- A While Program has an input variable, a block of commands and an
-- ouput variable
record WProgram : Set where
  constructor read_begin_write_
  field
    readInput   : Wvar
    blockProg   : Wcommand
    writeOutput : Wvar
  
