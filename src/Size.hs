{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-adt" @-}

module Size where

-- newtype Size = S {sizeVal :: Int}
{-@ type Size = Nat @-}
type Size = Int

{-@ assume ohmf :: i:Size -> {v:Size | v >= i} @-}
ohmf :: Size -> Size
ohmf = undefined

{-@ lazy ohm @-}
{-@ ohm :: Size @-}
ohm = ohmf ohm

-- will be hidden.
{-@ assume newSize :: s:Size -> {v:Size| v >= 0 && v < s} @-}
newSize :: Size -> Size
newSize = undefined -- Size . flip (-) 1 . sizeVal

-- {-@ lazy inf @-}
-- {-@ inf :: Size @-}
-- inf :: Size
-- inf = inf + 1

