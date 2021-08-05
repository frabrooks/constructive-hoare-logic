



-- Project Imports
open import Data using (Data-Implementation)
open import State using (State-Implementation)

module Language.ExampleProgs
  (𝔡 : Data-Implementation )
  (𝔖 : State-Implementation 𝔡 ) where

  open Data-Implementation 𝔡
  
  open import Language.Expressions 𝔡 𝔖
  open import Language.Mini-Imp 𝔡 𝔖

  
  Program = C

  -- Swap values of 𝒙 and 𝒚
  swap : Program
  swap = 𝒛 := 𝑣𝑎𝑙 𝒙 ;
         𝒙 := 𝑣𝑎𝑙 𝒚 ;
         𝒚 := 𝑣𝑎𝑙 𝒛 ;

{-
  Distinct, obviously works

  swap : Id → Id → Program
  swap 𝒙 𝒚 =
         𝒛 := 𝑣𝑎𝑙 𝒙 ;
         𝒙 := 𝑣𝑎𝑙 𝒚 ;
         𝒚 := 𝑣𝑎𝑙 𝒛 ;

  𝒛 == 𝒙 ∨ 𝒛 == 𝒚 obviously doesn't work

  swap : Id → Id → Program
  swap 𝒙 𝒚 =
         𝒛 := 𝑣𝑎𝑙 𝒙 ;
         𝒙 := 𝑣𝑎𝑙 𝒚 ;
         𝒚 := 𝑣𝑎𝑙 𝒛 ;


  𝒙 == 𝒚 then nothing happens but nothing needs
         to happen

  swap : Id → Id → Program
  swap 𝒙 𝒚 =
         𝒛 := 𝑣𝑎𝑙 𝒙 ;
         𝒙 := 𝑣𝑎𝑙 𝒙 ;
         𝒙 := 𝑣𝑎𝑙 𝒛 ;
  


-}


  -- Store absolute value of 𝒙 in 𝒛
  abs : Program
  abs = (𝔦𝔣 (𝑣𝑎𝑙 𝒙 ≥ 𝑐𝑜𝑛𝑠𝑡 ⓪)
         𝔱𝔥𝔢𝔫 (
           𝒛 := 𝑣𝑎𝑙 𝒙 ;)
         𝔢𝔩𝔰𝔢 (
           𝒛 := ── (𝑣𝑎𝑙 𝒙) ;)  );


  -- Euclids Algorithm for GCD
  gcd : (𝑿 𝒀 : Exp) → Program
  gcd 𝑿 𝒀 =
      𝒙 := 𝑿 ;
      𝒚 := 𝒀 ;
     (𝔴𝔥𝔦𝔩𝔢 (𝑛𝑜𝑡 ( 𝑣𝑎𝑙 𝒙 == 𝑣𝑎𝑙 𝒚 ))
      𝒹ℴ (𝔦𝔣 ( 𝑣𝑎𝑙 𝒙 > 𝑣𝑎𝑙 𝒚  )          
         𝔱𝔥𝔢𝔫 (
           𝒙 := 𝑣𝑎𝑙 𝒙 - 𝑣𝑎𝑙 𝒚 ;)
         𝔢𝔩𝔰𝔢 (
           𝒚 := 𝑣𝑎𝑙 𝒚 - 𝑣𝑎𝑙 𝒙 ;)  ;) );


  -- Multiply 𝑿 and 𝒀, and store in 𝒛, but
  -- without using multiplication operator
  -- ((11.4) in TSOP,Gries)
  -- {b ≥ 0 } add* { 𝒛 == 𝑿 * 𝒀 } 
  add* : (𝑿 𝒀 : Exp) → Program
  add* 𝑿 𝒀 =  
       𝒙 := 𝑿 ;
       𝒚 := 𝒀 ;
       𝒛 := 𝑐𝑜𝑛𝑠𝑡 ⓪ ;
      (𝔴𝔥𝔦𝔩𝔢
        (   ( 𝑣𝑎𝑙 𝒚 > 𝑐𝑜𝑛𝑠𝑡 ⓪ ∧ 𝑒𝑣𝑒𝑛〈 𝑣𝑎𝑙 𝒚 〉 )
          ∨ ( 𝑜𝑑𝑑〈 𝑣𝑎𝑙 𝒚 〉 )
        )
       𝒹ℴ (𝔦𝔣 ( 𝑒𝑣𝑒𝑛〈 𝑣𝑎𝑙 𝒚 〉 )
          𝔱𝔥𝔢𝔫 (
             𝒚 := 𝑣𝑎𝑙 𝒚 / 𝑐𝑜𝑛𝑠𝑡 ② ;
             𝒙 := 𝑣𝑎𝑙 𝒙 + 𝑣𝑎𝑙 𝒙    ;)
          𝔢𝔩𝔰𝔢 (
             𝒚 := 𝑣𝑎𝑙 𝒚 - 𝑐𝑜𝑛𝑠𝑡 ① ;
             𝒛 := 𝑣𝑎𝑙 𝒛 + 𝑣𝑎𝑙 𝒙    ;)    ;) );


