module Main where

import Data.Ratio

----- Algebras ------------------

data Iv = C Sd Iv
  deriving (Show, Read, Eq, Ord)

data Sd = Lft  | Rht  | Mid 
  deriving (Show, Read, Eq, Ord)

data Sdtwo = LL  | LT  | MT  | RT  | RR 
  deriving (Show, Read, Eq, Ord)

data Ag = LR Psd Ag | U Ah
  deriving (Show, Read, Eq, Ord)

data Ah = Fin Psd Ag | D Ah
  deriving (Show, Read, Eq, Ord)

data Psd = PLft  | PRht 
  deriving (Show, Read, Eq, Ord)

type Nat = Integer

type Pos = Integer

data Bg = Nz  | LRz Psd Bg | Uz Nat
  deriving (Show, Read, Eq, Ord)

----- Recursion operators -------

ivCoRec :: (alpha3022 -> ((alpha3022 -> (Sd, (Either Iv alpha3022))) -> Iv))
ivCoRec c f = (C (fst (f c)) (case (snd (f c)) of
 { Left v24195 -> v24195 ;
 Right c1 -> (ivCoRec c1 f) }))

ivDestr :: (Iv -> (Sd, Iv))
ivDestr (C d24183 v24182) = (d24183, v24182)

agCoRec :: (alpha3003 -> ((alpha3003 -> (Either (Psd, (Either Ag alpha3003)) (Either Ah alpha3004))) -> ((alpha3004 -> (Either (Psd, (Either Ag alpha3003)) (Either Ah alpha3004))) -> Ag)))
agCoRec c g f = (case (g c) of
 { Left o0 -> (LR (fst o0) (case (snd o0) of
 { Left p24181 -> p24181 ;
 Right c2 -> (agCoRec c2 g f) })) ;
 Right w0 -> (U (case w0 of
 { Left q24178 -> q24178 ;
 Right h1 -> (ahCoRec h1 g f) })) })

ahCoRec :: (alpha2984 -> ((alpha2985 -> (Either (Psd, (Either Ag alpha2985)) (Either Ah alpha2984))) -> ((alpha2984 -> (Either (Psd, (Either Ag alpha2985)) (Either Ah alpha2984))) -> Ah)))
ahCoRec c g f = (case (f c) of
 { Left h0 -> (Fin (fst h0) (case (snd h0) of
 { Left p24148 -> p24148 ;
 Right o1 -> (agCoRec o1 g f) })) ;
 Right w0 -> (D (case w0 of
 { Left q24145 -> q24145 ;
 Right c2 -> (ahCoRec c2 g f) })) })

agDestr :: (Ag -> (Either (Psd, Ag) Ah))
agDestr (LR a24115 p24114) = (Left (a24115, p24114))
agDestr (U q24113) = (Right q24113)

ahDestr :: (Ah -> (Either (Psd, Ag) Ah))
ahDestr (Fin a24112 p24111) = (Left (a24112, p24111))
ahDestr (D q24110) = (Right q24110)

natRec :: Nat -> a -> (Nat -> a -> a) -> a
natRec 0 g h = g
natRec n g h | n > 0 = h (n - 1) (natRec (n - 1) g h)

----- Program constants ---------

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

cCoGClause :: (Ag -> (Either (Psd, Ag) Ah))
cCoGClause = agDestr

psdPlus :: (Psd -> (Psd -> Sdtwo))
psdPlus PLft PLft = LL
psdPlus PLft PRht = MT
psdPlus PRht PLft = MT
psdPlus PRht PRht = RR

cCoGPsdTimes :: (Psd -> (Ag -> Ag))
cCoGPsdTimes = (\ a0 -> (\ p1 -> (case a0 of
 { PLft -> (cCoGMinus p1) ;
 PRht -> p1 })))

cCoHToCoG :: (Ah -> Ag)
cCoHToCoG = (\ q0 -> (agCoRec q0 (\ q1 -> (case (cCoHClause q1) of
 { Left ap24109 -> (Left ((fst ap24109), (Left (cCoGMinus (snd ap24109))))) ;
 Right q24108 -> (Right (Left q24108)) })) (\ p1 -> (case (cCoGClause p1) of
 { Left ap24107 -> (Left ((fst ap24107), (Left (cCoGMinus (snd ap24107))))) ;
 Right q24106 -> (Right (Left q24106)) }))))

cCoHClause :: (Ah -> (Either (Psd, Ag) Ah))
cCoHClause = ahDestr

cCoGMinus :: (Ag -> Ag)
cCoGMinus = (\ p0 -> (agCoRec p0 (\ p1 -> (case (agDestr p1) of
 { Left ap24105 -> (Left ((psdInv (fst ap24105)), (Left (snd ap24105)))) ;
 Right q24104 -> (Right (Right q24104)) })) (\ q1 -> (case (cCoHClause q1) of
 { Left ap24103 -> (Left ((psdInv (fst ap24103)), (Left (snd ap24103)))) ;
 Right q24102 -> (Right (Right q24102)) }))))

sdtwoInv :: (Sdtwo -> Sdtwo)
sdtwoInv LL = RR
sdtwoInv Main.LT = RT
sdtwoInv MT = MT
sdtwoInv RT = Main.LT
sdtwoInv RR = LL

cSdDisj :: (Sd -> (Maybe Psd))
cSdDisj = (\ d0 -> (case d0 of
 { Lft -> (Just PLft) ;
 Rht -> (Just PRht) ;
 Mid -> Nothing }))

sdSdtwoTimes :: (Sd -> (Sdtwo -> Sdtwo))
sdSdtwoTimes Lft i = (sdtwoInv i)
sdSdtwoTimes Rht i = i
sdSdtwoTimes Mid i = MT

cCoGAvcSatCoICl :: (Sdtwo -> (Ag -> (Ag -> (Sdtwo, (Sd, (Ag, Ag))))))
cCoGAvcSatCoICl = (\ i0 -> (\ p1 -> (\ p2 -> ((case (cCoGClause p1) of
 { Left ap24069 -> (case (cCoGClause p2) of
 { Left ap24071 -> (j (psdToSd (fst ap24069)) (psdToSd (fst ap24071)) i0) ;
 Right q24070 -> (j (psdToSd (fst ap24069)) Mid i0) }) ;
 Right q24066 -> (case (cCoGClause p2) of
 { Left ap24068 -> (j Mid (psdToSd (fst ap24068)) i0) ;
 Right q24067 -> (j Mid Mid i0) }) }), ((case (cCoGClause p1) of
 { Left ap24079 -> (case (cCoGClause p2) of
 { Left ap24081 -> (k (psdToSd (fst ap24079)) (psdToSd (fst ap24081)) i0) ;
 Right q24080 -> (k (psdToSd (fst ap24079)) Mid i0) }) ;
 Right q24076 -> (case (cCoGClause p2) of
 { Left ap24078 -> (k Mid (psdToSd (fst ap24078)) i0) ;
 Right q24077 -> (k Mid Mid i0) }) }), ((case (cCoGClause p1) of
 { Left ap24089 -> (case (cCoGClause p2) of
 { Left ap24091 -> (cCoGPsdTimes (psdInv (fst ap24089)) (snd ap24089)) ;
 Right q24090 -> (cCoGPsdTimes (psdInv (fst ap24089)) (snd ap24089)) }) ;
 Right q24086 -> (case (cCoGClause p2) of
 { Left ap24088 -> (cCoHToCoG q24086) ;
 Right q24087 -> (cCoHToCoG q24086) }) }), (case (cCoGClause p1) of
 { Left ap24099 -> (case (cCoGClause p2) of
 { Left ap24101 -> (cCoGPsdTimes (psdInv (fst ap24101)) (snd ap24101)) ;
 Right q24100 -> (cCoHToCoG q24100) }) ;
 Right q24096 -> (case (cCoGClause p2) of
 { Left ap24098 -> (cCoGPsdTimes (psdInv (fst ap24098)) (snd ap24098)) ;
 Right q24097 -> (cCoHToCoG q24097) }) })))))))

cCoGAvcToCoG :: ((Sdtwo, (Ag, Ag)) -> Ag)
cCoGAvcToCoG = (\ ipp0 -> (agCoRec ipp0 (\ ipp1 -> (let idpp2 = (cCoGAvcSatCoICl (fst ipp1) (fst (snd ipp1)) (snd (snd ipp1))) in (case (cSdDisj (fst (snd idpp2))) of
 { Nothing -> (Right (Right ((fst idpp2), (snd (snd idpp2))))) ;
 Just a24061 -> (Left (a24061, (Right ((sdSdtwoTimes (psdToSd a24061) (sdtwoInv (fst idpp2))), ((cCoGPsdTimes (psdInv a24061) (fst (snd (snd idpp2)))), (cCoGPsdTimes (psdInv a24061) (snd (snd (snd idpp2))))))))) }))) (\ ipp1 -> (let idpp2 = (cCoGAvcSatCoICl (fst ipp1) (fst (snd ipp1)) (snd (snd ipp1))) in (case (cSdDisj (fst (snd idpp2))) of
 { Nothing -> (Right (Right ((fst idpp2), (snd (snd idpp2))))) ;
 Just a24059 -> (Left (a24059, (Right ((sdSdtwoTimes (psdToSd a24059) (fst idpp2)), ((cCoGPsdTimes a24059 (fst (snd (snd idpp2)))), (cCoGPsdTimes a24059 (snd (snd (snd idpp2))))))))) })))))

cCoGAvToAvc :: (Ag -> (Ag -> (Sdtwo, (Ag, Ag))))
cCoGAvToAvc = (\ p0 -> (\ p1 -> ((case (cCoGClause p0) of
 { Left ap24035 -> (case (cCoGClause p1) of
 { Left ap24037 -> (psdPlus (fst ap24035) (fst ap24037)) ;
 Right q24036 -> (sdPlus (psdToSd (fst ap24035)) Mid) }) ;
 Right q24032 -> (case (cCoGClause p1) of
 { Left ap24034 -> (sdPlus Mid (psdToSd (fst ap24034))) ;
 Right q24033 -> MT }) }), ((case (cCoGClause p0) of
 { Left ap24045 -> (case (cCoGClause p1) of
 { Left ap24047 -> (cCoGPsdTimes (psdInv (fst ap24045)) (snd ap24045)) ;
 Right q24046 -> (cCoGPsdTimes (psdInv (fst ap24045)) (snd ap24045)) }) ;
 Right q24042 -> (case (cCoGClause p1) of
 { Left ap24044 -> (cCoHToCoG q24042) ;
 Right q24043 -> (cCoHToCoG q24042) }) }), (case (cCoGClause p0) of
 { Left ap24055 -> (case (cCoGClause p1) of
 { Left ap24057 -> (cCoGPsdTimes (psdInv (fst ap24057)) (snd ap24057)) ;
 Right q24056 -> (cCoHToCoG q24056) }) ;
 Right q24052 -> (case (cCoGClause p1) of
 { Left ap24054 -> (cCoGPsdTimes (psdInv (fst ap24054)) (snd ap24054)) ;
 Right q24053 -> (cCoHToCoG q24053) }) })))))

cStandardSplit :: (Rational -> (Maybe Bool))
cStandardSplit = (\ rat0 -> (if ((numerator rat0) > 0) then ((\ pos3 -> (Just (((pos3 * 2) * 2) < (denominator rat0)))) (numerator rat0)) else if ((numerator rat0) == 0) then ((Just True)) else (((\ pos3 -> (if (((pos3 * 2) * 2) <= (denominator rat0)) then (Just True) else Nothing)) (-(numerator rat0))))))

sDToInt :: (Sd -> Integer)
sDToInt Lft = -1
sDToInt Mid = 0
sDToInt Rht = 1

cSplitProp :: ((Nat -> Rational) -> Sd)
cSplitProp = (\ as0 -> (case (cStandardSplit (as0 2)) of
 { Nothing -> Lft ;
 Just w0 -> (if w0 then Mid else Rht) }))

cCoHClauseInv :: ((Either (Psd, Ag) Ah) -> Ah)
cCoHClauseInv = (\ atpq0 -> (ahCoRec atpq0 (\ atpq1 -> (case atpq1 of
 { Left ap24026 -> (Left ((fst ap24026), (Left (snd ap24026)))) ;
 Right q24025 -> (Right (Left q24025)) })) (\ atpq1 -> (case atpq1 of
 { Left ap24024 -> (Left ((fst ap24024), (Left (snd ap24024)))) ;
 Right q24023 -> (Right (Left q24023)) }))))

cCoGClauseInv :: ((Either (Psd, Ag) Ah) -> Ag)
cCoGClauseInv = (\ atpq0 -> (agCoRec atpq0 (\ atpq1 -> (case atpq1 of
 { Left ap24022 -> (Left ((fst ap24022), (Left (snd ap24022)))) ;
 Right q24021 -> (Right (Left q24021)) })) (\ atpq1 -> (case atpq1 of
 { Left ap24020 -> (Left ((fst ap24020), (Left (snd ap24020)))) ;
 Right q24019 -> (Right (Left q24019)) }))))

---------------------------------

cCoIAverage :: (Iv -> (Iv -> Iv))
cCoIAverage = (\ v -> (\ v0 -> (ivCoRec ((sdPlus (fst (ivDestr v)) (fst (ivDestr v0))), ((snd (ivDestr v)), (snd (ivDestr v0)))) (\ ivw -> (let jdvw = ((j (fst (ivDestr (fst (snd ivw)))) (fst (ivDestr (snd (snd ivw)))) (fst ivw)), ((k (fst (ivDestr (fst (snd ivw)))) (fst (ivDestr (snd (snd ivw)))) (fst ivw)), ((snd (ivDestr (fst (snd ivw)))), (snd (ivDestr (snd (snd ivw))))))) in ((fst (snd jdvw)), (Right ((fst jdvw), (snd (snd jdvw))))))))))

cCoIToCoG :: (Iv -> Ag)
cCoIToCoG = (\ v -> (agCoRec (PRht, v) (\ bv -> (case (fst (ivDestr (snd bv))) of
 { Lft -> (Left ((psdInv (fst bv)), (Right (PRht, (snd (ivDestr (snd bv))))))) ;
 Rht -> (Left ((fst bv), (Right (PLft, (snd (ivDestr (snd bv))))))) ;
 Mid -> (Right (Right ((fst bv), (snd (ivDestr (snd bv)))))) })) (\ bv -> (case (fst (ivDestr (snd bv))) of
 { Lft -> (Left ((psdInv (fst bv)), (Right (PLft, (snd (ivDestr (snd bv))))))) ;
 Rht -> (Left ((fst bv), (Right (PRht, (snd (ivDestr (snd bv))))))) ;
 Mid -> (Right (Right ((fst bv), (snd (ivDestr (snd bv)))))) }))))

cCoGToCoI :: (Ag -> Iv)
cCoGToCoI = (\ p -> (ivCoRec (PRht, (Left p)) (\ apq -> (case (snd apq) of
 { Left p24319 -> (case (agDestr p24319) of
 { Left ap24321 -> ((psdToSd (psdTimes (fst apq) (fst ap24321))), (Right ((psdInv (psdTimes (fst apq) (fst ap24321))), (Left (snd ap24321))))) ;
 Right q24320 -> (Mid, (Right ((fst apq), (Right q24320)))) }) ;
 Right q24316 -> (case (ahDestr q24316) of
 { Left ap24318 -> ((psdToSd (psdTimes (fst apq) (fst ap24318))), (Right ((psdTimes (fst apq) (fst ap24318)), (Left (snd ap24318))))) ;
 Right q24317 -> (Mid, (Right ((fst apq), (Right q24317)))) }) }))))

cCoGAverage :: (Ag -> (Ag -> Ag))
cCoGAverage = (\ p -> (\ p0 -> (cCoGAvcToCoG (cCoGAvToAvc p p0))))

cCauchyToSds :: ((Nat -> Rational) -> Iv)
cCauchyToSds = (\ as -> (ivCoRec as (\ as0 -> (let d = (cSplitProp as0) in (d, (Right (\ n -> (((2) * (as0 (n + 1))) - ((sDToInt d) % 1)))))))))

cSdsToCauchy :: (Iv -> (Nat -> Rational))
cSdsToCauchy = (\ v -> (\ n -> (natRec n (\ v0 -> (0)) (\ n0 -> (\ g -> (\ v0 -> (((g (snd (ivDestr v0))) + ((sDToInt (fst (ivDestr v0))) % 1)) / (2))))) v)))

cCoGToBG :: (Nat -> (Ag -> Bg))
cCoGToBG = (\ n -> (\ p -> (fst ((fst (natRec n ((\ p0 -> (Nz, (case (agDestr p0) of
 { Left ap24309 -> (LRz (fst ap24309) Nz) ;
 Right q24308 -> (Uz 0) }))), (\ q -> ((Left 0), (case (ahDestr q) of
 { Left ap24311 -> (Right ((fst ap24311), ((snd ap24311), Nz))) ;
 Right q24310 -> (Left 1) })))) (\ n0 -> (\ psf -> ((\ p0 -> ((snd ((fst psf) p0)), (case (agDestr p0) of
 { Left ap24269 -> (LRz (fst ap24269) (snd ((fst psf) (snd ap24269)))) ;
 Right q24266 -> (case (snd ((snd psf) q24266)) of
 { Left n24268 -> (Uz n24268) ;
 Right apbg24267 -> (LRz (fst apbg24267) (LRz PRht (snd (snd apbg24267)))) }) }))), (\ q -> ((snd ((snd psf) q)), (case (ahDestr q) of
 { Left ap24307 -> (Right ((fst ap24307), ((snd ap24307), (snd ((fst psf) (snd ap24307)))))) ;
 Right q24288 -> (case (snd ((snd psf) q24288)) of
 { Left n24306 -> (Left (n24306 + 1)) ;
 Right apbg24297 -> (Right ((fst apbg24297), ((agCoRec (Left (PLft, (fst (snd apbg24297)))) (\ atpq -> (case atpq of
 { Left ap24301 -> (Left ((fst ap24301), (Left (snd ap24301)))) ;
 Right q24300 -> (Right (Left q24300)) })) (\ atpq -> (case atpq of
 { Left ap24299 -> (Left ((fst ap24299), (Left (snd ap24299)))) ;
 Right q24298 -> (Right (Left q24298)) }))), (snd ((fst psf) (agCoRec (Left (PLft, (fst (snd apbg24297)))) (\ atpq -> (case atpq of
 { Left ap24305 -> (Left ((fst ap24305), (Left (snd ap24305)))) ;
 Right q24304 -> (Right (Left q24304)) })) (\ atpq -> (case atpq of
 { Left ap24303 -> (Left ((fst ap24303), (Left (snd ap24303)))) ;
 Right q24302 -> (Right (Left q24302)) })))))))) }) })))))))) p))))

cCoGToCoM :: (Ag -> Ag)
cCoGToCoM = (\ p -> (agCoRec p (\ p0 -> (case (agDestr p0) of
 { Left ap24253 -> (case (agDestr (snd ap24253)) of
 { Left ap24259 -> (case (fst ap24259) of
 { PLft -> (Left ((fst ap24253), (Right (snd ap24253)))) ;
 PRht -> (case (agDestr (snd ap24259)) of
 { Left ap24263 -> (case (fst ap24263) of
 { PLft -> (Right (Right (cCoHClauseInv (Left ((fst ap24253), (snd ap24259)))))) ;
 PRht -> (Left ((fst ap24253), (Right (snd ap24253)))) }) ;
 Right q24262 -> (Left ((fst ap24253), (Right (snd ap24253)))) }) }) ;
 Right q24258 -> (Left ((fst ap24253), (Right (snd ap24253)))) }) ;
 Right q24246 -> (case (ahDestr q24246) of
 { Left ap24250 -> (case (agDestr (snd ap24250)) of
 { Left ap24252 -> (case (fst ap24252) of
 { PLft -> (Right (Right (cCoHClauseInv (Left ap24250)))) ;
 PRht -> (Left ((fst ap24250), (Right (cCoGClauseInv (Right (cCoHClauseInv (Left (PRht, (snd ap24252))))))))) }) ;
 Right q24251 -> (Right (Right (cCoHClauseInv (Left ap24250)))) }) ;
 Right q24249 -> (Right (Right q24246)) }) })) (\ q -> (case (ahDestr q) of
 { Left ap24219 -> (case (agDestr (snd ap24219)) of
 { Left ap24225 -> (case (fst ap24225) of
 { PLft -> (case (agDestr (snd ap24225)) of
 { Left ap24229 -> (case (fst ap24229) of
 { PLft -> (Right (Right (cCoHClauseInv (Left ((fst ap24219), (snd ap24225)))))) ;
 PRht -> (Left ((fst ap24219), (Right (snd ap24219)))) }) ;
 Right q24228 -> (Left ((fst ap24219), (Right (snd ap24219)))) }) ;
 PRht -> (Left ((fst ap24219), (Right (snd ap24219)))) }) ;
 Right q24224 -> (Left ((fst ap24219), (Right (snd ap24219)))) }) ;
 Right q24212 -> (case (ahDestr q24212) of
 { Left ap24216 -> (case (agDestr (snd ap24216)) of
 { Left ap24218 -> (case (fst ap24218) of
 { PLft -> (Right (Right (cCoHClauseInv (Left ap24216)))) ;
 PRht -> (Left ((fst ap24216), (Right (cCoGClauseInv (Right (cCoHClauseInv (Left (PLft, (snd ap24218))))))))) }) ;
 Right q24217 -> (Right (Right (cCoHClauseInv (Left ap24216)))) }) ;
 Right q24215 -> (Right (Right q24212)) }) }))))

---------------------------------

main :: IO ()
main = putStrLn ""
