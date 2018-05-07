import Data.List (union, intersect, nub, elem)

type ConceptName = String
type RoleName = String
type InstanceName = String

data Instance = AtomicInstance InstanceName deriving(Eq, Show)
data Role = AtomicRole RoleName deriving(Eq, Show)
data Concept = AtomicConcept ConceptName | MAX | MIN | NOT Concept | AND Concept Concept | OR Concept Concept | ANY Role Concept | SOME Role Concept deriving(Eq, Show)


-- example
-- concept
male	= AtomicConcept "Male"
human	= AtomicConcept "Human"
animal	= AtomicConcept "Animal"
woman	= AtomicConcept "Woman"
dog	= AtomicConcept "Dog"
rich	= AtomicConcept "Rich"
poor	= AtomicConcept "Poor"
young	= AtomicConcept "Young"
leg	= AtomicConcept "Leg"
wing	= AtomicConcept "Wing"

-- role
hasChild	= AtomicRole "hasChild"
hasPart		= AtomicRole "hosPart"
isCarriedBy	= AtomicRole "isCarriedBy"

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

-- TBox statement
-- とりあえず原子的概念か否かは気にしない

data TBoxStatement = CEQ Concept Concept | CINC Concept Concept deriving(Eq, Show)

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

-- TBox Statement
tst0	= property `CEQ` (thing `AND` (ANY isPossessedOf human))
tst1	= murderer `CEQ` (human `AND` (SOME killed human))
tst2	= thief `CEQ` (human `AND` (SOME stole property))


-- ABox statement
data ABoxStatement = ConceptInst Concept Instance | RoleInst Role Instance Instance deriving(Eq,Show)

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



-- notをAtomicConceptの前に写す
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

-- あまり綺麗ではないが、型の形の判定
-- 原子か?
isAtomic :: Concept -> Bool
isAtomic (AtomicConcept _) = True
isAtomic (MAX) = True
isAtomic (MIN) = True
isAtomic (NOT (AtomicConcept _)) = True
isAtomic otherwise = False
-- そのほか
isAND :: Concept -> Bool
isAND (AND c0 c1) = True
isAND otherwise = False

isOR :: Concept -> Bool
isOR (OR c0 c1) = True
isOR otherwise = False

isANY :: Concept -> Bool
isANY (AND r c) = True
isANY otherwise = False

isSOME :: Concept -> Bool
isSOME (SOME r c) = True
isSOME otherwise = False

-- TListが矛盾もしくはMINを含むかの判定
-- (TName,Concept)とTListを引数にとり、TListに(TName, NOT Concept)が含まれるかを判定する関数
isContradict :: (TName,Concept) -> TList -> Bool
isContradict (tname,concept) tlist = elem (tname, (NOT concept)) tlist
-- 本体
checkTList :: TList -> Bool
checkTList tlist = not (hasMIN || hasContradiction)
	   where
		hasMIN = ([] /= [(k,v)| (k,v) <- tlist, v == MIN])
		hasContradiction = ([] /= [e| e <- tlist, isContradict e tlist]) 

-- TListで用いられているTNameの集合を入手
getTNames :: TList -> [TName]
getTNames tlist = nub [k| (k,v) <- tlist]

-- [TName]を受け取ってそこに含まれないTNameを生成する（INTに依存　もっというとmaxとsucが定義できることに依存）
generateTName :: [TName] -> TName
generateTName tnames = succ (maximum tnames)

-- TListが与えられた時、そのTListが充足可能かどうかを判定
-- 言うなれば肝の部分

-- 各条件式
andPropagatable :: (TName, Concept) -> TList -> Bool
andPropagatable (tname, (AND c1 c2)) tlist = not ((elem (tname, c1) tlist) && (elem (tname, c2) tlist))
andPropagatable c tlist = False

orPropagatable :: (TName, Concept) -> TList -> Bool
orPropagatable (tname, (OR c1 c2)) tlist = (not (elem (tname, c1) tlist)) && (not (elem (tname, c2) tlist))
orPropagatable c tlist = False

-- 本体
isSatisfiableTList :: TList -> Bool
isSatisfiableTList tlist
		   | andpropagatable /= [] = let (n, AND c1 c2) = head andpropagatable;  temp1 = (union tlist [(n,c1),(n,c2)]) in  (checkTList temp1) && (isSatisfiableTList temp1) 
		   | orpropagatable /= []  = let (n, OR c1 c2) = head orpropagatable;  temp1 = (union tlist [(n,c1)]); temp2 = (union tlist [(n,c2)])
		     		       	     in  ((checkTList temp1) && (isSatisfiableTList temp1)) || ((checkTList temp2) && (isSatisfiableTList temp2))
		   | otherwise = True
		     	       where andpropagatable = [x| x<-tlist, andPropagatable x tlist]
			       	     orpropagatable = [x| x<-tlist, orPropagatable x tlist]


-- この推論処理全体をラッピングする関数
initialname = 1 :: TName
isSatisfiable :: Concept -> Bool
isSatisfiable c = isSatisfiableTList [(initialname, toSimpleConcept c)]


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



---------------------------------------------------------------------------------
-- RListも含む場合へ拡張
type RList = [(Role, TName, TName)]

initialname' = 1 :: TName
isSatisfiable' :: Concept -> Bool
isSatisfiable' c = isSatisfiableTRList [(initialname, toSimpleConcept c)] []

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
						  ys = [y|(r',x',y)<-rlist, x==x', r==r'];
						  y = head ys;
						  tempt = union tlist [(y,c)]
		      		      	      in (checkTList tempt) && (isSatisfiableTRList tempt rlist)
		    | otherwise = True
		     	       where andpropagatable = [x| x<-tlist, andPropagatable x tlist]
			       	     orpropagatable = [x| x<-tlist, orPropagatable x tlist]
				     somepropagatable = [x|x<-tlist, somePropagatable x tlist rlist]
				     anypropagatable = [x|x<-tlist, anyPropagatable x tlist rlist]

-- someとanyの条件判定
somePropagatable :: (TName, Concept) -> TList -> RList -> Bool
somePropagatable (tname, (SOME r c)) tlist rlist = ([] == [(role,x,z)| (role,x,z) <- rlist, x==tname && role == r && elem (z,c) tlist])
somePropagatable temp tlist rlist = False

anyPropagatable :: (TName, Concept) -> TList -> RList -> Bool 
anyPropagatable (tname, (ANY r c)) tlist rlist = ([] /= [(role,x,y)| (role,x,y) <- rlist, x==tname && role == r && (not (elem (y,c) tlist))])
anyPropagatable temp tlist rlist = False
