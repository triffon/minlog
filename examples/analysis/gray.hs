module Main where

import Data.Ratio

----- Algebras ------------------

data Psd = PLft  | PRht 
  deriving (Show, Read, Eq, Ord)

data Iv = C Sd Iv
  deriving (Show, Read, Eq, Ord)

data Ag = LR Psd Ag | U Ah
  deriving (Show, Read, Eq, Ord)

data Ah = Fin Psd Ag | D Ah
  deriving (Show, Read, Eq, Ord)

data Sd = Lft  | Rht  | Mid 
  deriving (Show, Read, Eq, Ord)

data Sdtwo = LL  | LT  | MT  | RT  | RR 
  deriving (Show, Read, Eq, Ord)

type Nat = Integer

type Pos = Integer

data Bg = Nz  | LRz Psd Bg | Uz Nat
  deriving (Show, Read, Eq, Ord)

----- Recursion operators -------

agCoRec :: (alpha2490 -> ((alpha2490 -> (Either (Psd, (Either Ag alpha2490)) (Either Ah alpha2491))) -> ((alpha2491 -> (Either (Psd, (Either Ag alpha2490)) (Either Ah alpha2491))) -> Ag)))
agCoRec c g f = (case (g c) of
 { Left o0 -> (LR (fst o0) (case (snd o0) of
 { Left p18820 -> p18820 ;
 Right c2 -> (agCoRec c2 g f) })) ;
 Right w0 -> (U (case w0 of
 { Left q18817 -> q18817 ;
 Right h1 -> (ahCoRec h1 g f) })) })

ahCoRec :: (alpha2471 -> ((alpha2472 -> (Either (Psd, (Either Ag alpha2472)) (Either Ah alpha2471))) -> ((alpha2471 -> (Either (Psd, (Either Ag alpha2472)) (Either Ah alpha2471))) -> Ah)))
ahCoRec c g f = (case (f c) of
 { Left h0 -> (Fin (fst h0) (case (snd h0) of
 { Left p18787 -> p18787 ;
 Right o1 -> (agCoRec o1 g f) })) ;
 Right w0 -> (D (case w0 of
 { Left q18784 -> q18784 ;
 Right c2 -> (ahCoRec c2 g f) })) })

ivDestr :: (Iv -> (Sd, Iv))
ivDestr (C d18754 v18753) = (d18754, v18753)

ivCoRec :: (alpha2465 -> ((alpha2465 -> (Sd, (Either Iv alpha2465))) -> Iv))
ivCoRec c f = (C (fst (f c)) (case (snd (f c)) of
 { Left v18752 -> v18752 ;
 Right c1 -> (ivCoRec c1 f) }))

agDestr :: (Ag -> (Either (Psd, Ag) Ah))
agDestr (LR a18740 p18739) = (Left (a18740, p18739))
agDestr (U q18738) = (Right q18738)

ahDestr :: (Ah -> (Either (Psd, Ag) Ah))
ahDestr (Fin a18737 p18736) = (Left (a18737, p18736))
ahDestr (D q18735) = (Right q18735)

natRec :: Nat -> a -> (Nat -> a -> a) -> a
natRec 0 g h = g
natRec n g h | n > 0 = h (n - 1) (natRec (n - 1) g h)

----- Program constants ---------

psdInv :: (Psd -> Psd)
psdInv PLft = PRht
psdInv PRht = PLft

psdToSd :: (Psd -> Sd)
psdToSd PLft = Lft
psdToSd PRht = Rht

psdTimes :: (Psd -> (Psd -> Psd))
psdTimes PLft PLft = PRht
psdTimes PRht a = a
psdTimes a PRht = a

sdPlus :: (Sd -> (Sd -> Sdtwo))
sdPlus Lft Lft = LL
sdPlus Lft Mid = Main.LT
sdPlus Lft Rht = MT
sdPlus Mid Lft = Main.LT
sdPlus Mid Mid = MT
sdPlus Mid Rht = RT
sdPlus Rht Lft = MT
sdPlus Rht Mid = RT
sdPlus Rht Rht = RR

j :: (Sd -> (Sd -> (Sdtwo -> Sdtwo)))
j Lft Lft LL = LL
j Lft Lft Main.LT = MT
j Lft Lft MT = LL
j Lft Lft RT = MT
j Lft Lft RR = RR
j Lft Mid LL = Main.LT
j Lft Mid Main.LT = RT
j Lft Mid MT = Main.LT
j Lft Mid RT = RT
j Lft Mid RR = Main.LT
j Lft Rht LL = MT
j Lft Rht Main.LT = LL
j Lft Rht MT = MT
j Lft Rht RT = RR
j Lft Rht RR = MT
j Mid Lft LL = Main.LT
j Mid Lft Main.LT = RT
j Mid Lft MT = Main.LT
j Mid Lft RT = RT
j Mid Lft RR = Main.LT
j Mid Mid LL = MT
j Mid Mid Main.LT = LL
j Mid Mid MT = MT
j Mid Mid RT = RR
j Mid Mid RR = MT
j Mid Rht LL = RT
j Mid Rht Main.LT = Main.LT
j Mid Rht MT = RT
j Mid Rht RT = Main.LT
j Mid Rht RR = RT
j Rht Lft LL = MT
j Rht Lft Main.LT = LL
j Rht Lft MT = MT
j Rht Lft RT = RR
j Rht Lft RR = MT
j Rht Mid LL = RT
j Rht Mid Main.LT = Main.LT
j Rht Mid MT = RT
j Rht Mid RT = Main.LT
j Rht Mid RR = RT
j Rht Rht LL = LL
j Rht Rht Main.LT = MT
j Rht Rht MT = RR
j Rht Rht RT = MT
j Rht Rht RR = RR

k :: (Sd -> (Sd -> (Sdtwo -> Sd)))
k Lft Lft LL = Lft
k Lft Lft Main.LT = Lft
k Lft Lft MT = Mid
k Lft Lft RT = Mid
k Lft Lft RR = Mid
k Lft Mid LL = Lft
k Lft Mid Main.LT = Lft
k Lft Mid MT = Mid
k Lft Mid RT = Mid
k Lft Mid RR = Rht
k Lft Rht LL = Lft
k Lft Rht Main.LT = Mid
k Lft Rht MT = Mid
k Lft Rht RT = Mid
k Lft Rht RR = Rht
k Mid Lft LL = Lft
k Mid Lft Main.LT = Lft
k Mid Lft MT = Mid
k Mid Lft RT = Mid
k Mid Lft RR = Rht
k Mid Mid LL = Lft
k Mid Mid Main.LT = Mid
k Mid Mid MT = Mid
k Mid Mid RT = Mid
k Mid Mid RR = Rht
k Mid Rht LL = Lft
k Mid Rht Main.LT = Mid
k Mid Rht MT = Mid
k Mid Rht RT = Rht
k Mid Rht RR = Rht
k Rht Lft LL = Lft
k Rht Lft Main.LT = Mid
k Rht Lft MT = Mid
k Rht Lft RT = Mid
k Rht Lft RR = Rht
k Rht Mid LL = Lft
k Rht Mid Main.LT = Mid
k Rht Mid MT = Mid
k Rht Mid RT = Rht
k Rht Mid RR = Rht
k Rht Rht LL = Mid
k Rht Rht Main.LT = Mid
k Rht Rht MT = Mid
k Rht Rht RT = Rht
k Rht Rht RR = Rht

sDToInt :: (Sd -> Integer)
sDToInt Lft = -1
sDToInt Mid = 0
sDToInt Rht = 1

natToInt :: (Nat -> Integer)
natToInt 0 = 0
natToInt nat | nat > 0 = ((natToInt (nat - 1)) + 1)

sqrtaux :: (Rational -> (Nat -> Rational))
sqrtaux rat 0 = ((natToInt 1) % 1)
sqrtaux rat n | n > 0 = (((sqrtaux rat (n - 1)) + (rat / (sqrtaux rat (n - 1)))) / (2))

sqrt :: (Rational -> (Nat -> Rational))
sqrt rat n = (sqrtaux rat (n + 1))

---------------------------------

stog :: ((Psd, Iv) -> Ag)
stog = (\ bv -> (agCoRec bv (\ bv0 -> (case (fst (ivDestr (snd bv0))) of
 { Lft -> (Left ((psdInv (fst bv0)), (Right (PRht, (snd (ivDestr (snd bv0))))))) ;
 Rht -> (Left ((fst bv0), (Right (PLft, (snd (ivDestr (snd bv0))))))) ;
 Mid -> (Right (Right ((fst bv0), (snd (ivDestr (snd bv0)))))) })) (\ bv0 -> (case (fst (ivDestr (snd bv0))) of
 { Lft -> (Left ((psdInv (fst bv0)), (Right (PLft, (snd (ivDestr (snd bv0))))))) ;
 Rht -> (Left ((fst bv0), (Right (PRht, (snd (ivDestr (snd bv0))))))) ;
 Mid -> (Right (Right ((fst bv0), (snd (ivDestr (snd bv0)))))) }))))

gtos :: (Psd -> (Ag -> Iv))
gtos = (\ a -> (\ p -> (ivCoRec (a, (Left p)) (\ apq -> (case (snd apq) of
 { Left p18844 -> (case (agDestr p18844) of
 { Left ap18846 -> ((psdToSd (psdTimes (fst apq) (fst ap18846))), (Right ((psdInv (psdTimes (fst apq) (fst ap18846))), (Left (snd ap18846))))) ;
 Right q18845 -> (Mid, (Right ((fst apq), (Right q18845)))) }) ;
 Right q18841 -> (case (ahDestr q18841) of
 { Left ap18843 -> ((psdToSd (psdTimes (fst apq) (fst ap18843))), (Right ((psdTimes (fst apq) (fst ap18843)), (Left (snd ap18843))))) ;
 Right q18842 -> (Mid, (Right ((fst apq), (Right q18842)))) }) })))))

gminus :: (Ag -> Ag)
gminus = (\ p -> (agCoRec p (\ p0 -> (case (agDestr p0) of
 { Left ap18836 -> (Left ((psdInv (fst ap18836)), (Left (snd ap18836)))) ;
 Right q18835 -> (Right (Right q18835)) })) (\ q -> (case (ahDestr q) of
 { Left ap18834 -> (Left ((psdInv (fst ap18834)), (Left (snd ap18834)))) ;
 Right q18833 -> (Right (Right q18833)) }))))

av :: (Iv -> (Iv -> Iv))
av = (\ v -> (\ v0 -> (ivCoRec ((sdPlus (fst (ivDestr v)) (fst (ivDestr v0))), ((snd (ivDestr v)), (snd (ivDestr v0)))) (\ ivw -> (let jdvw = ((j (fst (ivDestr (fst (snd ivw)))) (fst (ivDestr (snd (snd ivw)))) (fst ivw)), ((k (fst (ivDestr (fst (snd ivw)))) (fst (ivDestr (snd (snd ivw)))) (fst ivw)), ((snd (ivDestr (fst (snd ivw)))), (snd (ivDestr (snd (snd ivw))))))) in ((fst (snd jdvw)), (Right ((fst jdvw), (snd (snd jdvw))))))))))

ctos :: ((Nat -> Rational) -> Iv)
ctos = (\ as -> (ivCoRec as (\ as0 -> (let d = (if ((numerator (as0 2)) > 0) then ((\ pos0 -> (if (((pos0 * 2) * 2) < (denominator (as0 2))) then Mid else Rht)) (numerator (as0 2))) else if ((numerator (as0 2)) == 0) then (Mid) else (((\ pos0 -> (if (((pos0 * 2) * 2) <= (denominator (as0 2))) then Mid else Lft)) (-(numerator (as0 2)))))) in (d, (Right (\ n -> (((2) * (as0 (n + 1))) - ((sDToInt d) % 1)))))))))

stoc :: (Iv -> (Nat -> Rational))
stoc = (\ v -> (\ n -> (natRec n (\ v0 -> (0)) (\ n0 -> (\ s -> (\ v0 -> (((s (snd (ivDestr v0))) + ((sDToInt (fst (ivDestr v0))) % 1)) / (2))))) v)))

rattosqrt :: (Rational -> (Nat -> Rational))
rattosqrt = Main.sqrt

gtobg :: (Nat -> (Ag -> Bg))
gtobg = (\ n0 -> (fst (natRec n0 ((\ p2 -> Nz), (\ q2 -> (Left 0))) (\ n2 -> (\ psf3 -> ((\ p4 -> (case (agDestr p4) of
 { Left ap18826 -> (LRz (fst ap18826) ((fst psf3) (snd ap18826))) ;
 Right q18823 -> (case ((snd psf3) q18823) of
 { Left n18825 -> (Uz n18825) ;
 Right apbg18824 -> (LRz (fst apbg18824) (if (n2 == 0) then Nz else ((LRz PRht (snd (snd apbg18824)))))) }) })), (\ q4 -> (case (ahDestr q4) of
 { Left ap18832 -> (Right ((fst ap18832), ((snd ap18832), ((fst psf3) (snd ap18832))))) ;
 Right q18829 -> (case ((snd psf3) q18829) of
 { Left n18831 -> (Left (n18831 + 1)) ;
 Right apbg18830 -> (Right ((fst apbg18830), ((LR PLft (fst (snd apbg18830))), ((fst psf3) (LR PLft (fst (snd apbg18830))))))) }) }))))))))

---------------------------------

main :: IO ()
main = putStrLn ""