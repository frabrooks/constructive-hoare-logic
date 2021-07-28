



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

  -- Swap values of 𝔁 and 𝔂
  swap : Program
  swap = 𝔃 := 𝑣𝑎𝑙 𝔁 ;
         𝔁 := 𝑣𝑎𝑙 𝔂 ;
         𝔂 := 𝑣𝑎𝑙 𝔃 ;


  -- Store absolute value of 𝔁 in 𝔃
  abs : Program
  abs = (𝔦𝔣 (𝑣𝑎𝑙 𝔁 ≥ 𝑐𝑜𝑛𝑠𝑡 ⓪)
         𝔱𝔥𝔢𝔫
           𝔃 := 𝑣𝑎𝑙 𝔁 ;
         𝔢𝔩𝔰𝔢
           𝔃 := ── (𝑣𝑎𝑙 𝔁)  ;);


  -- Euclids Algorithm for GCD
  gcd : Program
  gcd =  𝔁 := 𝑣𝑎𝑙 𝑿 ;
         𝔂 := 𝑣𝑎𝑙 𝒀 ;
        (𝔴𝔥𝔦𝔩𝔢 (𝑛𝑜𝑡 ( 𝑣𝑎𝑙 𝔁 == 𝑣𝑎𝑙 𝔂 ))
         𝒹ℴ (𝔦𝔣 ( 𝑣𝑎𝑙 𝔁 > 𝑣𝑎𝑙 𝔂  )          
            𝔱𝔥𝔢𝔫                           
              𝔁 := 𝑣𝑎𝑙 𝔁 - 𝑣𝑎𝑙 𝔂 ;    
            𝔢𝔩𝔰𝔢                           
              𝔂 := 𝑣𝑎𝑙 𝔂 - 𝑣𝑎𝑙 𝔁 ;  ););


