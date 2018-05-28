module DLreasoner (..) where


-- 循環ありのTBox

import Data.List (union, intersect, nub, elem)
import Test.HUnit

import Debug.Trace

-- 型の定義
type ConceptName = String
type RoleName = String
type InstanceName = String

data Instance = AtomicInstance InstanceName deriving(Eq, Show, Read)
data Role = AtomicRole RoleName deriving(Eq, Show, Read)
data Concept = AtomicConcept ConceptName | MAX | MIN | NOT Concept | AND Concept Concept | OR Concept Concept | ANY Role Concept | SOME Role Concept deriving(Eq, Show, Read)

-- TBox statement
-- とりあえず原子的概念か否かは気にしない 左が右を含む
data TBoxStatement = CEQ Concept Concept | CINC Concept Concept deriving(Eq, Show)
type TBox = [TBoxStatement]

-- ABox statement
data ABoxStatement = ConceptInst Concept Instance | RoleInst Role Instance Instance deriving(Eq,Show)



-- notをAtomicConceptの前に写す(NNFへの変換）
toSimpleConcept :: Concept -> Concept
toSimpleConcept (NOT c) = toSimpleConceptNot c
toSimpleConcept (AtomicConcept c) = AtomicConcept c
toSimpleConcept (MAX) = MAX
toSimpleConcept (MIN) = MIN
toSimpleConcept (AND c0 c1) = AND (toSimpleConcept c0) (toSimpleConcept c1)
toSimpleConcept (OR c0 c1) = OR (toSimpleConcept c0) (toSimpleConcept c1)
toSimpleConcept (ANY r c) = ANY r (toSimpleConcept c)
toSimpleConcept (SOME r c) = SOME r (toSimpleConcept c)

toSimpleConceptNot :: Concept -> Concept
toSimpleConceptNot (AtomicConcept a) = NOT (AtomicConcept a)
toSimpleConceptNot (MAX) = MIN
toSimpleConceptNot (MIN) = MAX
toSimpleConceptNot (NOT c) = c
toSimpleConceptNot (AND c0 c1) = OR (toSimpleConcept (NOT c0)) (toSimpleConcept (NOT c1))
toSimpleConceptNot (OR c0 c1) = AND  (toSimpleConcept (NOT c0)) (toSimpleConcept (NOT c1))
toSimpleConceptNot (ANY r c) = SOME r (toSimpleConcept (NOT c))
toSimpleConceptNot (SOME r c) = ANY r (toSimpleConcept (NOT c))



-- 推論アルゴリズム　充足可能性判定
-- 論文のS
type TName = Int
type TList = [(TName, Concept)]
-- RListも含む場合へ拡張
type RList = [(Role, TName, TName)]


-- TListが矛盾もしくはMINを含むかの判定
-- (TName,Concept)とTListを引数にとり、TListに(TName, NOT Concept)が含まれるかを判定する関数
isContradict :: (TName,Concept) -> TList -> Bool
isContradict (tname,concept) tlist = elem (tname, (NOT concept)) tlist

-- 本体
checkTList :: TList -> Bool
checkTList tlist = not (hasMIN || hasContradiction)
	   where
		hasMIN = ([] /= [(k,v)| (k,v) <- tlist, v == MIN])
		hasContradiction = ([] /= [e | e <- tlist, isContradict e tlist]) 


-- TListで用いられているTNameの集合を入手
getTNames :: TList -> [TName]
getTNames tlist = nub [k | (k,v) <- tlist]

-- [TName]を受け取ってそこに含まれないTNameを生成する（INTに依存　もっというとmaxとsucが定義できることに依存）
generateTName :: [TName] -> TName
generateTName tnames = succ (maximum tnames)


-- TListが与えられた時、そのTListが充足可能かどうかを判定
-- 言うなれば肝の部分
--------------
initialname = 1 :: TName

isSatisfiable :: Concept -> Bool
isSatisfiable c = isSatisfiableTRList [(initialname, toSimpleConcept c)] []

isSatisfiableTRList :: TList -> RList -> Bool
isSatisfiableTRList tlist rlist
		    | andpropagatable /= [] = let (n, AND c1 c2) = head andpropagatable;  temp1 = (union tlist [(n,c1),(n,c2)]) in  (checkTList temp1) && (isSatisfiableTRList temp1 rlist) 
		    | orpropagatable /= []  = let (n, OR c1 c2) = head orpropagatable;  temp1 = (union tlist [(n,c1)]); temp2 = (union tlist [(n,c2)])
		     		       	     in  ((checkTList temp1) && (isSatisfiableTRList temp1 rlist)) || ((checkTList temp2) && (isSatisfiableTRList temp2 rlist))
		    | somepropagatable /= [] = let (x, SOME r c) = head somepropagatable;
		      		       	       	   y = generateTName $ getTNames tlist
		      		       	       	   tempt = union tlist [(y,c)];
						   tempr = union rlist [(r,x,y)]
					       in  (checkTList tempt) && (isSatisfiableTRList tempt tempr)
                    | anypropagatable /= [] = let (x, ANY r c) = head anypropagatable;
						  ys = [y |(r',x',y)<-rlist, x==x', r==r'];
						  y = head ys;
						  tempt = union tlist [(y,c)]
		      		      	      in (checkTList tempt) && (isSatisfiableTRList tempt rlist)
		    | otherwise = True
		     	       where andpropagatable = [x | x<-tlist, andPropagatable x tlist]
			       	     orpropagatable = [x | x<-tlist, orPropagatable x tlist]
				     somepropagatable = [x |x<-tlist, somePropagatable x tlist rlist]
				     anypropagatable = [x |x<-tlist, anyPropagatable x tlist rlist]

-- 各条件式
-- andとorの条件判定
andPropagatable :: (TName, Concept) -> TList -> Bool
andPropagatable (tname, (AND c1 c2)) tlist = not ((elem (tname, c1) tlist) && (elem (tname, c2) tlist))
andPropagatable c tlist = False

orPropagatable :: (TName, Concept) -> TList -> Bool
orPropagatable (tname, (OR c1 c2)) tlist = (not (elem (tname, c1) tlist)) && (not (elem (tname, c2) tlist))
orPropagatable c tlist = False

-- someとanyの条件判定
somePropagatable :: (TName, Concept) -> TList -> RList -> Bool
somePropagatable (tname, (SOME r c)) tlist rlist = ([] == [(role,x,z)| (role,x,z) <- rlist, x==tname && role == r && elem (z,c) tlist])
somePropagatable temp tlist rlist = False

anyPropagatable :: (TName, Concept) -> TList -> RList -> Bool 
anyPropagatable (tname, (ANY r c)) tlist rlist = ([] /= [(role,x,y)| (role,x,y) <- rlist, x==tname && role == r && (not (elem (y,c) tlist))])
anyPropagatable temp tlist rlist = False



-- TBoxStatementに関する推論
-- 入力されたTBoxStatemantを今GHCiにロードされている原始概念を使って置き換え、そのStatementの充足可能性を判定する

inferenceTBoxStatement :: TBoxStatement -> Bool
inferenceTBoxStatement (CINC c d) = not $ isSatisfiable ( (NOT c ) `AND` d)
inferenceTBoxStatement (CEQ c d) = (inferenceTBoxStatement (CINC c d)) && (inferenceTBoxStatement (CINC d c))



-- Inference TBox
-- TBoxを与えてその全てを同時に充足することが可能かを判定する
-- CEQはCINCを相互にかけたものと等しいと仮定した

-- checkTBox :: TBox -> Bool
-- checkTBox tbox =  not (isSatisfiable  (AND MAX (NOT (tboxToConcept tbox))))

-- general inclusion axiomを含んだ場合の推論
-- cbarはNNFとする
isSatisfiableGeneral :: Concept -> TBox -> Bool
isSatisfiableGeneral c tbox = isSatisfiableGeneralTRList cbar [(initialname, toSimpleConcept c), (initialname, cbar)] []
  where cbar =  tboxToConcept tbox

isSatisfiableGeneralTRList :: Concept -> TList -> RList -> Bool
isSatisfiableGeneralTRList cbar tlist rlist
		    | andpropagatable /= [] = let (n, AND c1 c2) = head andpropagatable;  temp1 = (union tlist [(n,c1),(n,c2)]) in  (checkTList temp1) && (isSatisfiableGeneralTRList cbar temp1 rlist) 
		    | orpropagatable /= []  = let (n, OR c1 c2) = head orpropagatable;  temp1 = (union tlist [(n,c1)]); temp2 = (union tlist [(n,c2)])
                                             in  ((checkTList temp1) && (isSatisfiableGeneralTRList cbar temp1 rlist)) || ((checkTList temp2) && (isSatisfiableGeneralTRList cbar temp2 rlist))
                    | anypropagatable /= [] = let (x, ANY r c) = head anypropagatable;
						  ys = [y |(r',x',y)<-rlist, x==x', r==r'];
						  y = head ys;
						  tempt = union tlist [(y,c)]
		      		      	      in (checkTList tempt) && (isSatisfiableGeneralTRList cbar tempt rlist)
		    | somepropagatable' /= [] = let (x, SOME r c) = head somepropagatable';
		      		       	       	    y = generateTName $ getTNames tlist
		      		       	       	    tempt = union tlist [(y,c)];
						    tempr = union rlist [(r,x,y)]
					       in  (checkTList tempt) && (isSatisfiableGeneralTRList cbar tempt tempr)
                    | generalpropagatable /= [] = let name = head generalpropagatable;
                                                      tempt = union tlist [(name,cbar)]
                                               in trace ((show tlist) ++ "\n" ++ (show rlist) ++ "\n\n") ((checkTList tempt) && (isSatisfiableGeneralTRList cbar tempt rlist))
		    | otherwise = True
		     	       where andpropagatable = [x | x<-tlist, andPropagatable x tlist]
			       	     orpropagatable = [x | x<-tlist, orPropagatable x tlist]
				     somepropagatable' = [x |x<-tlist, somePropagatable' x cbar tlist rlist]
				     anypropagatable = [x |x<-tlist, anyPropagatable x tlist rlist]
                                     generalpropagatable = [name | name <- getTNames tlist, generalPropagatable name cbar tlist]

-- これのテスト（テキストの例）
w = AtomicConcept "W"
e1 = AtomicConcept "E1"
e2 = AtomicConcept "E2"
h = AtomicRole "h"
gtscbar = ((NOT e1) `OR` ( w `AND` (ANY h ( e1 `OR` e2 ) ) ))   `AND`  ( ( (NOT w) `OR` (SOME h ((NOT e1) `AND` (NOT e2) ))) `OR` e1 )
gttl = [(initialname,w),(initialname,gtscbar)]


isSatisfiableGeneralTR :: TBox -> TList -> RList -> Bool
isSatisfiableGeneralTR tbox tlist rlist = isSatisfiableGeneralTRList cbar tlist rlist
  where cbar = tboxToConcept tbox

--test




-- isSatisfiableGeneralTRList gtscbar gttl []


-- 新しい個体が増えた時の処理
generalPropagatable :: TName -> Concept -> TList -> Bool
generalPropagatable name cbar tlist = not $ elem (name,cbar) tlist

--test
-- isSatisfiableGeneralTRList fortestcbar fortesttl fortestrl 


-- someの場合の条件判定（追加）
somePropagatable' :: (TName, Concept) -> Concept ->  TList -> RList -> Bool
somePropagatable' (tname, (SOME r c)) cbar tlist rlist = (not (makeLoop (tname, (SOME r c)) cbar tlist rlist))  && ([] == [(role,x,z)| (role,x,z) <- rlist, x==tname && role == r && elem (z,c) tlist])
somePropagatable' temp cbar tlist rlist = False

-- somePropagetable'のテストはいいや


--ループが起こらないかを判定　同じ存在量化子で始まる概念が　過去にその量化子の一階層上の概念であったことはないか
-- 本当はここで推移的閉包を取るべき　ループを起こすならTrueを返す
makeLoop :: (TName, Concept) -> Concept -> TList -> RList -> Bool
makeLoop (tname, (SOME r c)) cbar tlist rlist = ( [] /= [((SOME r c),x) | (role,x,y) <- rlist, y==tname && elem (x,(SOME r c)) tlist] )

fortestconcept = (SOME (AtomicRole "hasChild") (SOME (AtomicRole "hasWife") (AtomicConcept "Female")))
fortesttl = [(3::TName, (AtomicConcept "Female")),
             (2::TName, fortestconcept),
             (2::TName, (SOME (AtomicRole "hasWife") (AtomicConcept "Female"))),
             (1::TName, fortestconcept)
            ]
fortestrl = [((AtomicRole "hasWife"), 2::TName, 3::TName),
             ((AtomicRole "hasChild"), 1::TName, 2::TName)
            ]
fortestcbar = fortestconcept
fortestin = (2::TName, fortestconcept)

-- makeLoop fortestin fortestcbar fortesttl fortestrl


tboxToConcept :: TBox -> Concept
tboxToConcept [] = MAX --本当は違うかも
tboxToConcept ((d `CINC` c):ts) = toSimpleConcept $  (AND (OR (NOT c) d)  (tboxToConcept ts) )

eqToInc :: TBox -> TBox
eqToInc [] = []
eqToInc (t:ts) = open (t) ++ eqToInc (ts)
                 where
                   open (a `CEQ` b) = [(CINC a b), (CINC b a)]
                   open (a `CINC` b) = [(a `CINC` b)]
-- toConcept :: TBoxStatement -> Concept
-- toConcept (CINC c d) = ((NOT c) `AND` d )



------------------------ examples

-- example
-- concept
male	= AtomicConcept "Male"
female  = AtomicConcept "Female"
human	= AtomicConcept "Human"
animal	= AtomicConcept "Animal"
woman	= AtomicConcept "Woman"
dog	= AtomicConcept "Dog"
rich	= AtomicConcept "Rich"
poor	= AtomicConcept "Poor"
young	= AtomicConcept "Young"
leg	= AtomicConcept "Leg"
wing	= AtomicConcept "Wing"


-- compounded concept
man	      = male `AND` human
notanimal     = NOT animal
maleOrWoman   = male `OR` woman

dogParent     = dog `AND` (SOME hasChild dog)
c0	      = ANY hasChild woman
normal	      = human `AND` (NOT (rich `OR` poor))
normal'	      = human `AND` ((NOT rich) `AND` (NOT poor))
c1	      = (SOME hasPart leg) `OR` (SOME hasPart wing)
nothavchi     = human `AND` (ANY hasChild MIN)


-- for entailment test
compc = (( male `OR` female ) `AND` ( SOME stole ( thing `AND` (ANY isPossessedOf ( male `OR` female))) ) ) `AND`
        ( (NOT male) `AND` (NOT female))

-- --------- test
a = [(10,male),(20,normal)] :: TList
b = union a [(10,(NOT male))]

tc = [(0,(AND male (NOT male)))] :: [(TName,Concept)]
tc2= union tc [(1,human)]
tc3= (male `OR` (NOT male))

-- for test tautology
tt1 = NOT (male `AND` (NOT male))
tt2 = male `OR` (NOT male)
tt3 = ((NOT male) `OR` ((NOT human) `OR` male))

-- example
-- atomic concept
property  = AtomicConcept "Property"
thing	  = AtomicConcept "Thing"
murderer  = AtomicConcept "Murderer"
thief	  = AtomicConcept "Thief"

-- atomic role
isPossessedOf	= AtomicRole "isPossessedOf"
killed		= AtomicRole "killed"
stole		= AtomicRole "stole"
-- role
hasChild	= AtomicRole "hasChild"
hasPart		= AtomicRole "hosPart"
isCarriedBy	= AtomicRole "isCarriedBy"

-- example
-- instance
iJohn	= AtomicInstance  "John"
iTom	= AtomicInstance  "Tom"
iJerry	= AtomicInstance  "Jerry"
iObject = AtomicInstance  "Object"

-- instance statement
ast0 = ConceptInst human iJohn
ast1 = ConceptInst human iTom
ast2 = ConceptInst human iJerry
ast3 = ConceptInst (NOT (thief `AND` murderer)) iJohn
ast4 = RoleInst killed iTom iJerry
ast5 = RoleInst stole iTom iObject
ast6 = RoleInst isPossessedOf iObject iJerry

-- TBox
-- TBox Statement
tst0	= property `CEQ` (thing `AND` (ANY isPossessedOf human))
tst1	= murderer `CEQ` (human `AND` (SOME killed human))
tst2	= thief `CEQ` (human `AND` (SOME stole property))

-- unfoldedTbox
-- or and 注意
tbox1 = [
  (AtomicConcept "Teacher") `CEQ` (AtomicConcept "Sensei")
  ]
                                

tbox2 = [
  (AtomicConcept "Property'") `CEQ` (thing `AND`
                                     ( ANY isPossessedOf
                                       ((AtomicConcept "male'") `OR` (AtomicConcept "female`")))) :: TBoxStatement ,
  (AtomicConcept "Murderer'") `CEQ` (((AtomicConcept "male'") `OR` (AtomicConcept "female`")) `AND`
                                     ( SOME killed
                                       ((AtomicConcept "male'") `OR` (AtomicConcept "female`")))) :: TBoxStatement ,
  (AtomicConcept "Thief'") `CEQ` ( ((AtomicConcept "male'") `OR` (AtomicConcept "female`")) `AND`
                                   ( SOME stole
                                     (AtomicConcept "Property'"))) :: TBoxStatement ,
  (AtomicConcept "Human'") `CEQ` ((AtomicConcept "male'") `OR` (AtomicConcept "female`")) :: TBoxStatement,
  human `CINC` (male `OR` female)
  ]



-- Inference test
t_thief =  ( ((AtomicConcept "male'") `AND` (AtomicConcept "female`")) `AND`
                                   ( SOME stole
                                     (AtomicConcept "Property'")))
t_human =  ((AtomicConcept "male'") `AND` (AtomicConcept "female`"))

t_st1 = (t_human `CINC` t_thief)
t_st2 = (t_thief `CINC` t_human)
t_st3 = (t_human `CEQ` t_thief)



------------------- Unit Test

-- test1 = (assertEqual "for (hoge 1)," [1] (hoge 1))
-- runTestTT

tests = TestList [ TestLabel "Taut1 Satisfiability"  (TestCase  (assertEqual (show tt1) True (isSatisfiable tt1))),
                   TestLabel "Taut2 Satisfiability"  (TestCase  (assertEqual (show tt2) True (isSatisfiable tt2))),
                   TestLabel "Taut3 Satisfiability"  (TestCase  (assertEqual (show tt3) True (isSatisfiable tt3))),
                   TestLabel "inclusion test1"  (TestCase  (assertEqual (show t_st1) True (inferenceTBoxStatement t_st1))),
                   TestLabel "inclusion test2"  (TestCase  (assertEqual (show t_st2) False (inferenceTBoxStatement t_st2))),
                   TestLabel "inclusion test2"  (TestCase  (assertEqual (show t_st3) False (inferenceTBoxStatement t_st3)))
                 ]


-- あまり綺麗ではないが、型の形の判定
-- 原子か?
-- isAtomic :: Concept -> Bool
-- isAtomic (AtomicConcept _) = True
-- isAtomic (MAX) = True
-- isAtomic (MIN) = True
-- isAtomic (NOT (AtomicConcept _)) = True
-- isAtomic otherwise = False
-- そのほか
-- isAND :: Concept -> Bool
-- isAND (AND c0 c1) = True
-- isAND otherwise = False

-- isOR :: Concept -> Bool
-- isOR (OR c0 c1) = True
-- isOR otherwise = False

-- isANY :: Concept -> Bool
-- isANY (AND r c) = True
-- isANY otherwise = False

-- isSOME :: Concept -> Bool
-- isSOME (SOME r c) = True
-- isSOME otherwise = False
