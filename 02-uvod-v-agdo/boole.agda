module boole where

data 𝔹 : Set where
    𝕥 : 𝔹
    𝕗 : 𝔹

if_then_else_ : {A : Set} → 𝔹 → A → A → A
if 𝕥 then x else y = x
if 𝕗 then x else y = y
