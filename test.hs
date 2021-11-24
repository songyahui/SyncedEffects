
module Blank where

{-@
twice :: forall < gpost :: a -> a -> Bool
              , gpre :: a -> Bool
              , twicepre :: a -> Bool
              , twicepost :: a -> a -> Bool
              >.
       {x::a<gpre>, w::a<gpost x> |- a<gpost w> <: a<twicepost x>}
       {x::a<twicepre> |- a<gpost x> <: a<gpre>}
       {x::a<twicepre> |- a<twicepre> <: a<gpre>}
       g:(z:a<gpre> -> a<gpost z>)
    -> x:a<twicepre> -> a<twicepost x>
@-}
twice g x = g (g x)

{-@quad :: forall < fpost :: a -> a -> Bool
              , fpre :: a -> Bool
              , quadpre :: a -> Bool
              , quadpost :: a -> a -> Bool
              >.
              
        {x::a<twicepre> -> <twicepost x>}
        {f::(z:a<fpre> -> a<fpost z>) |- (z:a<fpre> -> a<fpost z>) <: (z:a<twicepre> -> a<twicepre z>)}
       f:(z:a<fpre> -> a<fpost z>)
    -> x:a<quadpre> -> a<quadpost x>
@-}
quad f x = let g = twice twice f in g x
-- twice <: twice.g.pre -> twice.g.post


{-@ goo :: x:{v:Nat | v < 101} -> {v:Nat | v < 99} @-}
goo :: Int -> Int
goo x = 20

{-@ koo :: (x:{v:Nat | v < 100} -> {v:Nat | v < 100}) -> {v:Nat | v < 100} -> Nat @-}
koo :: (Int -> Int) -> Int -> Int
koo g x = g x

test = koo goo 0

-- goo real <: goo formal
-- (x:{v:Nat | v < 101} -> {v:Nat | v < 99}) <: (x:{v:Nat | v < 100} -> {v:Nat | v < 100})