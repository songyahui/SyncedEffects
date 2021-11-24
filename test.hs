
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
        {f::a<fpre> |- a<fpre> <: a<twicepre>}
       f:(z:a<fpre> -> a<fpost z>)
    -> x:a<quadpre> -> a<quadpost x>
@-}
quad f x = 
    let g = twice twice f 
    in g x
 