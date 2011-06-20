module Reverse where


import Prelude hiding (reverse)

reverse [] = []
reverse (x:xs) = reverse xs ++ [x]

-- reverse with a continuation
revC :: [a] -> ([a] -> [a]) -> [a]
revC []     cont = cont []
revC (x:xs) cont = revC xs (\ys -> cont (ys ++ [x]))

-- New reverse.
reverse2 xs = revC xs id

{-

In general:

revC xs cont == cont (reverse xs)

Proof:
[] case:
    revC [] cont
==    {- defintion -}
    cont []
==    {- [] case of reversen -}
    cont (reverse [])

(x:xs) case:

    revC (x:xs) cont
==    {- definition -}
    revC xs (\ys -> cont (ys ++ [x]))
==    {- induction -}
    (\ys -> cont (ys ++ [x])) (reverse xs)
==    {- simplify -}
    cont (reverse xs ++ [x])
==    {- (x:xs) case of reverse -}
    cont (reverse (x:xs))

Observation. Every continuation is of form for 'revC xs id'

  \zs -> zs ++ ys (for some ys)

Proof.
-----
Base case:

 revC is initially called with id == \zs -> zs
  id == \zs -> zs == \zs -> zs ++ []

Inductive case:

   \zs -> cont (zs ++ [x])
== \zs -> (\zs' -> zs' ++ ys) (zs ++ [x])    for some ys
== \zs -> (zs ++ [x]) ++ ys
==    {- associativity of (++) -}
    \zs -> zs ++ ([x] ++ ys)
==
    \zs -> zs ++ (x:ys)

Since:

  revC xs cont == cont (reverse xs)

we now have:

  revC xs (\zs -> zs ++ ys) == (\zs -> zs ++ ys) (reverse xs)
                            == reverse xs ++ ys

  Let's define a new function 'rev' with almost the same specification:
  *** THIS IS THE MOST MAGICAL PART OF THE WHOLE DERIVATION FOR ME***

  rev xs ys == reverse xs ++ ys

Before we had:

   reverse2 == revC xs id

We can now equivalently say:

   reverse2 == rev xs []

Proof:

  revC xs id == reverse xs ++ ys == rev xs []

Now let's see where this new specification takes us:

{- Law -}
rev xs ys == reverse xs ++ ys

Case (x:xs)
   rev (x:xs) ys
==   {- rev xs ys == reverse xs ++ ys -}
   reverse (x:xs) ++ ys
==   {- (x:xs) case of reverse -}
   reverse xs ++ [x]) ++ ys
==   {- associativity of (++) -}
   reverse xs ++ ([x] ++ ys)
==   {- (x:xs) case of (++) -}
   reverse xs ++ (x:([] ++ ys))
==   {- []-case of (++) -}
   reverse xs ++ (x:ys)
==   {- rev xs ys = reverse xs ++ ys -}
   rev xs (x:ys)

Case []
   rev [] ys
==   {- rev xs ys == reverse xs ++ ys -}
   reverse [] ++ ys
==   {- [] case of reverse -}
   [] ++ ys
==   {- [] case of (++) -}
   ys

Therefore:
-}
rev     [] ys = ys
rev (x:xs) ys = rev xs (x:ys)
