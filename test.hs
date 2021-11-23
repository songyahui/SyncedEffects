
module Blank where

-- this is simply, a blank file.
{-@
twice :: forall < gpost :: a -> a -> Bool
              , gpre :: a -> Bool
              , rpre :: a -> Bool
              , rpost :: a -> a -> Bool
              >.
       {x::a<gpre>, w::a<gpost x> |- a<gpost w> <: a<rpost x>}
       {x::a<gpre> |- a<gpost x> <: a<gpre>}
       {x::a<rpre> |- a<rpre> <: a<gpre>}
       g:(z:a<gpre> -> a<gpost z>)
    -> x:a<rpre> -> a<rpost x>
@-}
twice g x = g (g x)

{-@
quad :: forall < gpost :: a -> a -> Bool
              , gpre :: a -> Bool
              , rpre :: a -> Bool
              , rpost :: a -> a -> Bool
              >.
       {x::a<gpre>, w::a<gpost x> |- a<gpost w> <: a<rpost x>}
       {x::a<gpre> |- a<gpost x> <: a<gpre>}
       {x::a<rpre> |- a<rpre> <: a<gpre>}
       g:(z:a<gpre> -> a<gpost z>)
    -> x:a<rpre> -> a<rpost x>
@-}
quad :: (t -> t) -> t -> t
quad = twice twice 

{-@
foo1 :: forall < gpost :: a -> a -> Bool
              , gpre :: a -> Bool
              , rpre :: a -> Bool
              , rpost :: a -> a -> Bool
              >.
       {x::a<gpre>, w::a<gpost x> |- a<gpost w> <: a<rpost x>}
       {x::a<gpre> |- a<gpost x> <: a<gpre>}
       {x::a<rpre> |- a<rpre> <: a<gpre>}
       g:(z:a<gpre> -> a<gpost z>)
    -> x:a<rpre> -> a<rpost x>
@-}
foo1 :: (t -> t) -> t -> t
foo1 = twice quad  -- //2^4  (16) 

foo2 :: (t -> t) -> t -> t
foo2 = quad twice  -- //+16  (4^2) 

foo3 :: (t -> t) -> t -> t
foo3 = quad quad   -- //+256  (4^4)


inc :: Num a => a -> a
inc x = x + 1

main :: IO ()
main = print (foo3 inc 0)