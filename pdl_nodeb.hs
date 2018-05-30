import Data.List (union, intersect, nub, elem, sort)
import Test.HUnit

-- import Debug.Trace

-- import qualified DLreasoner as DL




-- データ型の定義


type ConceptName = String
type RoleName = String
type InstanceName = String

-- data Instance = AtomicInstance InstanceName deriving(Eq, Show, Read)
data TNumber = No Int deriving (Eq, Show, Read)

data PRole = AtomicPRole RoleName TNumber deriving(Eq, Show, Read)

data PConcept = AtomicPConcept ConceptName TNumber | TOP | BOTTOM | NOT PConcept | AND PConcept PConcept | OR PConcept PConcept | ANY PRole PConcept | SOME PRole PConcept deriving(Eq, Show, Read)

-- P-DL用のTBox(本当はいらないかもしれない）
-- data PTBoxStatement = CEQ PConcept PConcept | CINC PConcept PConcept deriving (Eq, Show)
-- 今回はCINCしか実装しない
data PTBoxStatement = CINC PConcept PConcept deriving (Eq, Show)
type PTBox = [PTBoxStatement]

-- Tableau計算で用いるもの
type PTName = Int
type PTList = [(PTName, PConcept)]
type PRList = [(PRole, PTName, PTName)]
type TableauNode = (PTList, PRList)

-- その時点の各Tableauの内容を表したもの
type PararellTableauNode = [TableauNode]
-- 非決定性計算で使用
type PararellTableauNodeList = [PararellTableauNode]




-- 処理部分

-- NNFへの変換
toSimplePConcept :: PConcept -> PConcept
toSimplePConcept (NOT c) = toSimplePConceptNot c
toSimplePConcept (AtomicPConcept c num ) = AtomicPConcept c num
toSimplePConcept (TOP) = TOP
toSimplePConcept (BOTTOM) = BOTTOM
toSimplePConcept (AND c0 c1) = AND (toSimplePConcept c0) (toSimplePConcept c1)
toSimplePConcept (OR c0 c1) = OR (toSimplePConcept c0) (toSimplePConcept c1)
toSimplePConcept (ANY r c) = ANY r (toSimplePConcept c)
toSimplePConcept (SOME r c) = SOME r (toSimplePConcept c)

toSimplePConceptNot :: PConcept -> PConcept
toSimplePConceptNot (AtomicPConcept a num) = NOT (AtomicPConcept a num)
toSimplePConceptNot (TOP) = BOTTOM
toSimplePConceptNot (BOTTOM) = TOP
toSimplePConceptNot (NOT c) = c
toSimplePConceptNot (AND c0 c1) = OR (toSimplePConcept (NOT c0)) (toSimplePConcept (NOT c1))
toSimplePConceptNot (OR c0 c1) = AND  (toSimplePConcept (NOT c0)) (toSimplePConcept (NOT c1))
toSimplePConceptNot (ANY r c) = SOME r (toSimplePConcept (NOT c))
toSimplePConceptNot (SOME r c) = ANY r (toSimplePConcept (NOT c))


-- 充足可能性判定のための小関数群

-- (PTName, PConcept)を取り、それがPTListと矛盾しているかを判定する
-- これは実は、二重否定規則を使っていないので効率的とは言えない（が、矛盾は必ず発見できる)
isContradict :: (PTName, PConcept) -> PTList -> Bool
isContradict (ptname, pconcept) ptlist = elem (ptname, (NOT pconcept)) ptlist

-- isContradictを利用して、PTListが矛盾していないかどうかを調べる
-- 全ての要素について矛盾せず、また、BOTTOMを含まない
-- 矛盾していたら
isContradictPTList :: PTList -> Bool
isContradictPTList ptlist = (hasBOTTOM || hasContradiction)
  where
    hasBOTTOM = not $ null  [(k,v)| (k,v) <- ptlist, v == BOTTOM]
    hasContradiction = not $ null  [e | e <- ptlist, isContradict e ptlist]


-- PTName関係
-- PTListで用いられているPTNameの集合を入手
getPTNamesFromPTList :: PTList -> [PTName]
getPTNamesFromPTList ptlist = nub [k | (k,v) <- ptlist]

-- PRListで用いられているPTNameの集合を入手
getPTNamesFromPRList :: PRList -> [PTName]
getPTNamesFromPRList prlist = nub $ foldl union [] [[n1, n2] | (r, n1, n2) <- prlist]

-- TableauNodeで用いられているPTNameの集合を入手
getPTNamesFromTableauNode :: TableauNode -> [PTName]
getPTNamesFromTableauNode (ptlist, prlist) = union (getPTNamesFromPTList ptlist) (getPTNamesFromPRList prlist)

-- PararellTableauNode間で使われているPTNameの集合を入手
-- グローバルにユニークなPTNameの発行を行うために利用する
{-
　　　分散システムのはずが全てのノードに横断してID発行を行なっているので注意
　　　　（実際は乱数生成を利用すればいいので問題ない）
-}
getPTNamesFromPararellTableauNode :: PararellTableauNode -> [PTName]
getPTNamesFromPararellTableauNode tableaunode_list = foldl union [] (map getPTNamesFromTableauNode tableaunode_list)

-- PararellTableauNodeListからのPTListの取得
--    多分いらない。複数分岐を跨いだユニークなID発行なんて不要

-- PTNameの集合からそこにない名前を作る
generatePTName :: [PTName] -> PTName
generatePTName ptnames = succ (maximum ptnames)



-- TBox関係
-- TBoxを表現する概念Cbarを作る
ptboxToPConcept :: PTBox -> PConcept
ptboxToPConcept [] = TOP
ptboxToPConcept ((d `CINC` c):ts) = toSimplePConcept $  (AND (OR (NOT c) d)  (ptboxToPConcept ts) )



-- P-DLの推論の本体 reportingとmembershipの実装

-- delta
-- その概念の担当先　今推論しているノード番号と概念を受け取ってその概念の担当先に返す
-- Atomicかその否定の時のみその概念の定義場所を返す、それ以外は今推論しているノードを返す
delta :: PConcept -> TNumber -> TNumber
delta (AtomicPConcept c n) tn = n
delta (NOT (AtomicPConcept c n)) tn = n
delta pc tn = tn

-- membership
-- individual(PTName)とpconceptと今推論しているノードとPararellTableauNodeを受け取って,その組みが含まれているかどうかを調べる
-- 本当は必要ないけど気持ちを書くために場合分けを行う
membership :: PTName -> PConcept -> TNumber -> PararellTableauNode -> Bool
membership ptname pconcept (No tnum) pararellt
  | origin == tnum = elem (ptname, pconcept) (tlist tnum pararellt)
  | otherwise         = elem (ptname, pconcept) (tlist origin pararellt)
    where
      (No origin) = delta pconcept (No tnum)
      tlist n para =  fst (pararellt !! n)

-- 本体 reporting
-- 加えたいコンセプトのPTNameと、加えたいPConceptと、推論を行うTNumberと、TBoxの集合と、開始時点のPararellTNode
-- を受け取って、PararellTNodeの条件下で、TNumberの推論において、PTName:PConceptが充足可能か否かを返す
-- 内部では推論を一段進めて[pararellTNode]を呼び出す

-- and  c1 and c2 に対し, r(c1)を行なった後自分のtlistに結果を追加しの世界にr(c2)を行う

-- 引数はparatab' 証明したい関係が入ってなければとりあえず自分のTListに入れる


reporting :: PTName -> PConcept -> TNumber -> [PConcept] -> PararellTableauNode -> [PararellTableauNode]
reporting ptname pconcept (No tnumber) cbars paratab'
  | paratab == []          = [] :: [PararellTableauNode]
  
  | andpropagatable /= []  = let (n, AND c1 c2) = head andpropagatable;
                                 temp1  = addPTList n c1 (No tnumber) [paratab];
                                 temp2  = addPTList n c2 (No tnumber) temp1;
                                 temp3  = concat $ map (\p -> reporting n c1 (delta c1 (No tnumber)) cbars p) temp2;
                                 
                                 temp4  = concat $ map (\p -> reporting n c2 (delta c2 (No tnumber)) cbars p) temp3;
                             in
                                 checkPararellTableauNodes temp4

  | orpropagatable /= []   = let (n, OR c1 c2) =head orpropagatable;
                                 temp1_1 = addPTList n c1 (No tnumber) [paratab];
                                 temp1_2 = concat $ map (\p -> reporting n c1 (delta c1 (No tnumber)) cbars p) temp1_1;
                                 temp2_1 = addPTList n c2 (No tnumber) [paratab];
                                 temp2_2 = concat $ map (\p -> reporting n c2 (delta c2 (No tnumber)) cbars p) temp2_1;
                             in
                                 concat $ map checkPararellTableauNodes [temp1_2, temp2_2]

  | generalpropagatable /= [] = let name = head generalpropagatable;
                                    temp1 = addPTList name my_cbar (No tnumber) [paratab]
                                    temp2 = concat $ map (\p -> reporting name my_cbar (delta my_cbar (No tnumber)) cbars p) temp1;
                                in
                                    checkPararellTableauNodes temp2

                                 
  | otherwise = [paratab]
    where
      temp   = take 1 (checkPararellTableauNodes (addPTList ptname pconcept (No tnumber) [paratab'])) :: [PararellTableauNode]
      paratab = case temp of
                  [] -> [] :: PararellTableauNode
                  _  -> head temp
      my_tab    = paratab !! tnumber
      my_ptlist = fst my_tab
      my_prlist = snd my_tab
      my_cbar   = cbars !! tnumber
      andpropagatable = [x | x <- my_ptlist, andPropagatable x my_ptlist]
      orpropagatable  = [x | x <- my_ptlist,  orPropagatable x my_ptlist]
      generalpropagatable = [name | name <- getPTNamesFromTableauNode my_tab, generalPropagatable name my_cbar my_ptlist]


-- 計算の便宜のため、帰ってきた[PararellTableauNode]のPTListにも関係を追加する
addPTList :: PTName -> PConcept -> TNumber -> [PararellTableauNode] -> [PararellTableauNode]
addPTList ptname pconcept (No tnumber) paratabs
  = map (adder (No tnumber))  paratabs
    where
      add :: TableauNode -> TableauNode
      add tab = (union [(ptname, pconcept)] (fst tab) , (snd tab) :: PRList) :: TableauNode
      adder :: TNumber -> [TableauNode] -> [TableauNode]
      adder (No n) tabs = (take n tabs) ++ [add (tabs !! n)] ++ (drop (n+1) tabs)

-- [PararellTableauNode]の中の矛盾しているPararellTableauNodeを削除
checkPararellTableauNodes :: [PararellTableauNode] -> [PararellTableauNode]
checkPararellTableauNodes ptnodes = nub [pnode | pnode <- ptnodes, not (isContradictPararellTableauNode pnode) ]

-- TableauNodeが矛盾しているか
isContradictTableauNode :: TableauNode -> Bool
isContradictTableauNode tnode = isContradictPTList $ fst tnode

-- PararellTablauNodeが矛盾しているか
isContradictPararellTableauNode :: PararellTableauNode -> Bool
isContradictPararellTableauNode ptnode = or  $ map isContradictTableauNode ptnode


-- 諸拡大条件 そのまま
andPropagatable :: (PTName, PConcept) -> PTList  ->  Bool
andPropagatable (ptname, (AND c1 c2)) my_ptlist =
  not ((elem (ptname, c1) my_ptlist) && (elem (ptname, c2) my_ptlist))
andPropagatable c my_ptlist = False

orPropagatable :: (PTName, PConcept) -> PTList -> Bool
orPropagatable (ptname, (OR c1 c2)) my_ptlist =
  (not (elem (ptname, c1) my_ptlist)) && (not (elem (ptname, c2) my_ptlist))
orPropagatable c my_ptlist = False

generalPropagatable :: PTName -> PConcept -> PTList -> Bool
generalPropagatable name cbar ptlist = not $ elem (name, cbar) ptlist



-- ラッピング関数　TBoxsにおいてn番目のノードで包含関係を推論
initialptname = 1

isSatisfiable :: PConcept -> TNumber -> [PTBox] -> Bool
isSatisfiable pconcept tnumber ptboxs = not ( null $ reporting initialptname pconcept tnumber cbars paratab )
  where
    paratab =  take (length cbars) (repeat ([],[]))
    cbars  =  map ptboxToPConcept ptboxs

isSatisfiablePTBoxStatement :: PTBoxStatement -> TNumber -> [PTBox] -> Bool
isSatisfiablePTBoxStatement (a `CINC` b) tnumber ptboxs = not $ isSatisfiable pconcept tnumber ptboxs
  where
    pconcept = ((NOT a) `AND` b)



-- テスト

-- テスト用の諸定義
-- PConcept
human0 = AtomicPConcept "Human" (No 0)
hasChild0 = AtomicPRole "hasChild" (No 0)

human1 = AtomicPConcept "Human" (No 1)
hasChild1 = AtomicPRole "hasChild" (No 1)

f0 = AtomicPConcept "F" (No 0)
b0 = AtomicPConcept "B" (No 0)
p1 = AtomicPConcept "P" (No 1)
a0 = AtomicPConcept "A" (No 0)
c1 = AtomicPConcept "C" (No 1)
d2 = AtomicPConcept "D" (No 2)

ptbox0 = [(f0 `CINC` b0)]
ptbox1 = [(b0 `CINC` p1), ((NOT f0) `CINC` p1)]

ptbox1_0 = [(b0 `CINC` a0)]
ptbox1_1 = [(c1 `CINC` b0)]
ptbox1_2 = [(d2 `CINC` c1)]
ptboxs1 = [ptbox1_0, ptbox1_1, ptbox1_2]

-- NNFへの変換 toSimplePConcept
test1_1_arg = NOT ( TOP )
test1_1_ans = BOTTOM

test1_2_arg = NOT ( NOT BOTTOM )
test1_2_ans = BOTTOM

test1_3_arg = NOT ( human1 `AND` ( NOT human1 ) )
test1_3_ans = (NOT human1) `OR` human1

test1_4_arg = NOT (human1 `OR` (NOT human1))
test1_4_ans = (NOT human1) `AND` human1


-- 終了条件の判定　isContradictPTList
test2_1_arg = [(1, human1), (1, NOT human1)]
test2_1_ans = True

test2_2_arg = [(1, human1), (2, NOT human1)]
test2_2_ans = False

test2_3_arg = [(1, human1), (1, BOTTOM)]
test2_3_ans = True

-- 終了条件判定　矛盾する概念の存在 isContradict
test3_1_arg2 = [(2, NOT human1), (1, human1)]
test3_1_arg1 = (1, human1)
test3_1_ans = False

-- 同一タブロー内（つまりは１つの分散されたノード内）のPTNameを返す getPTNamesFromTableauNode
-- 本当はソートしなきゃイコールにならないけどまあ
test4_1_arg = ([(1, human1), (3, NOT human1), (5, OR human1 human1)],
               [(hasChild1, 1, 3), (hasChild1, 6, 7)]) :: TableauNode
test4_1_ans = [1,3,5,6,7]                                                 
                                                 
-- 全てのノード内で今使われているPTNameの集合を得る
test5_1_p1 = ([(1, human0), (3, NOT human0), (5, OR human0 human0)],
               [(hasChild0, 1, 3), (hasChild0, 6, 7)]) :: TableauNode
test5_1_p2 = ([(2, human1), (3, NOT human1), (9, OR human1 human1)],
               [(hasChild1, 13, 17), (hasChild1, 6, 9)]) :: TableauNode
test5_1_arg = [test5_1_p1, test5_1_p2] :: PararellTableauNode                
test5_1_ans = [1,2,3,5,6,7,9,13,17]


-- ある概念の所属するノードをTNumberで答える delta
test6_1_arg1 = human0
test6_1_arg2 = No 1 :: TNumber
test6_1_ans  = No 0

test6_2_arg1 = NOT (human0 `AND` (NOT human0))
test6_2_arg2 = No 1 :: TNumber
test6_2_ans  = No 1 :: TNumber

test6_3_arg1 = NOT human1
test6_3_arg2 = No 0 :: TNumber
test6_3_ans  = No 1 :: TNumber


-- PConceptとPTNameの組が存在しているかどうかの問い合わせ（を行なっているように見せる） membership
test7_1_arg1 = 5 :: PTName
test7_1_arg2 = OR human0 human0 :: PConcept
test7_1_arg3 = No 0 :: TNumber
test7_1_arg4 = test5_1_arg :: PararellTableauNode
test7_1_ans = True

test7_2_arg1 = 3 :: PTName
test7_2_arg2 = NOT human1 :: PConcept
test7_2_arg3 = No 0 :: TNumber
test7_2_arg4 = test5_1_arg :: PararellTableauNode
test7_2_ans = True

test7_3_arg1 = 4 :: PTName
test7_3_arg2 = NOT human1 :: PConcept
test7_3_arg3 = No 0 :: TNumber
test7_3_arg4 = test5_1_arg :: PararellTableauNode
test7_3_ans = False


-- PTBoxの内容をCBarに変換
test8_1_arg = ptbox0
test8_1_ans = ((NOT b0) `OR` f0) `AND` TOP

test8_2_arg = ptbox1
test8_2_ans = ((NOT p1) `OR` b0) `AND` (((NOT p1) `OR` (NOT f0)) `AND` TOP)


-- ANDのテスト reporting
-- 自分の内部での推論
test9_1_arg1 = 1 :: PTName
test9_1_arg2 = (AND f0 b0) :: PConcept
test9_1_arg3 = (No 0) :: TNumber
test9_1_arg4 = [TOP,TOP] :: [PConcept]
test9_1_arg5 = [([(1,AND f0 b0)],[]),([],[])] :: PararellTableauNode
-- reporting test9_1_arg1  test9_1_arg2 test9_1_arg3 test9_1_arg4 test9_1_arg5
test9_1_ans  = [ [
                   ([(1, b0), (1, f0),(1, AND f0 b0)],
                    []),
                   ([],[])
                 ]
               ]

--　自分の外部との矛盾する推論
test9_2_arg1 = 1 :: PTName
test9_2_arg2 = (AND f0 p1) :: PConcept
test9_2_arg3 = (No 0) :: TNumber
test9_2_arg4 = [TOP,TOP] :: [PConcept]
test9_2_arg5 = [([],[]),([(1,NOT p1)],[])] :: PararellTableauNode -- 矛盾する
-- reporting test9_2_arg1  test9_2_arg2 test9_2_arg3 test9_2_arg4 test9_2_arg5
test9_2_ans  = []


-- ORのテスト reporting
-- 自分の内部での推論
test9_3_arg1 = 1 :: PTName
test9_3_arg2 = (OR f0 b0) :: PConcept
test9_3_arg3 = (No 0) :: TNumber
test9_3_arg4 = [TOP,TOP] :: [PConcept]
test9_3_arg5 = [([],[]),([],[])] :: PararellTableauNode
-- reporting test9_3_arg1  test9_3_arg2 test9_3_arg3 test9_3_arg4 test9_3_arg5
test9_3_ans  = [[([(1, f0),(1,OR f0 b0)],[]),([],[])],[([(1, b0),(1, OR f0 b0)],[]),([],[])]]

-- 外部も合わせた推論
test9_4_arg1 = 1 :: PTName
test9_4_arg2 = (OR f0 p1) :: PConcept
test9_4_arg3 = (No 0) :: TNumber
test9_4_arg4 = [TOP,TOP] :: [PConcept]
test9_4_arg5 = [([],[]),([],[])] :: PararellTableauNode
-- reporting test9_4_arg1  test9_4_arg2 test9_4_arg3 test9_4_arg4 test9_4_arg5


-- AND OR generalのテスト 論文の例3.5-2
test9_5_arg1 = 1 :: PTName
test9_5_arg2 = p1 :: PConcept
test9_5_arg3 = (No 1) :: TNumber
test9_5_arg4 = [(NOT b0) `OR` f0 , ((NOT p1) `OR` b0) `AND` ((NOT p1) `OR` (NOT f0))] :: [PConcept]
test9_5_arg5 = [([],[]),([],[])] :: PararellTableauNode
-- reporting test9_5_arg1  test9_5_arg2 test9_5_arg3 test9_5_arg4 test9_5_arg5
test9_5_ans = []

-- AND OR generalのテスト 論文の例3.5-1 推移関係
test9_6_arg1 = 1 :: PTName
test9_6_arg2 = (AND a0 (NOT d2)) :: PConcept
test9_6_arg3 = (No 2) :: TNumber
test9_6_arg4 = map ptboxToPConcept ptboxs1
test9_6_arg5 = [([],[]),([],[]),([],[])] :: PararellTableauNode
-- reporting test9_6_arg1  test9_6_arg2 test9_6_arg3 test9_6_arg4 test9_6_arg5
test9_6_ans = []


-- ラッパー関数のテスト isSatisfiablePTBoxStatement
test10_1_arg1 = d2 `CINC` a0 :: PTBoxStatement
test10_1_arg2 = (No 2) :: TNumber
test10_1_arg3 = ptboxs1
test10_1_ans = True
-- isSatisfiablePTBoxStatement test10_1_arg1 test10_1_arg2 test10_1_arg3 


-- テスト本体定義
tests = TestList [ TestLabel "NNF 1" (TestCase (assertEqual (show test1_1_arg) test1_1_ans (toSimplePConcept test1_1_arg))),
                   TestLabel "NNF 2" (TestCase (assertEqual (show test1_2_arg) test1_2_ans (toSimplePConcept test1_2_arg))),
                   TestLabel "NNF 3" (TestCase (assertEqual (show test1_3_arg) test1_3_ans (toSimplePConcept test1_3_arg))),
                   TestLabel "NNF 4" (TestCase (assertEqual (show test1_4_arg) test1_4_ans (toSimplePConcept test1_4_arg))),
                   
                   TestLabel "Contradiction 1" (TestCase (assertEqual (show test2_1_arg) test2_1_ans (isContradictPTList test2_1_arg))),
                   TestLabel "Contradiction 2" (TestCase (assertEqual (show test2_2_arg) test2_2_ans (isContradictPTList test2_2_arg))),
                   TestLabel "Contradiction 3" (TestCase (assertEqual (show test2_3_arg) test2_3_ans (isContradictPTList test2_3_arg))),
                   
                   TestLabel "isContradict" (TestCase (assertEqual (show test3_1_arg1) test3_1_ans (isContradict test3_1_arg1 test3_1_arg2))),
                   
                   TestLabel "getPTNames" (TestCase (assertEqual (show test4_1_arg) test4_1_ans (getPTNamesFromTableauNode test4_1_arg))),
                   
                    TestLabel "getPTNames PararellTableau" (TestCase (assertEqual (show test5_1_arg) test5_1_ans (sort (getPTNamesFromPararellTableauNode test5_1_arg)))),
                    
                    TestLabel "Delta operation 1" (TestCase (assertEqual ((show test6_1_arg1) ++ (show test6_1_arg2)) test6_1_ans (delta test6_1_arg1 test6_1_arg2))),
                    TestLabel "Delta operation 2" (TestCase (assertEqual ((show test6_2_arg1) ++ (show test6_2_arg2)) test6_2_ans (delta test6_2_arg1 test6_2_arg2))),
                    TestLabel "Delta operation 3" (TestCase (assertEqual ((show test6_3_arg1) ++ (show test6_3_arg2)) test6_3_ans (delta test6_3_arg1 test6_3_arg2))),
                    
                    TestLabel "membership operation 1" (TestCase (assertEqual ((show test7_1_arg1) ++ (show test7_1_arg2) ++ (show test7_1_arg3)) test7_1_ans (membership test7_1_arg1 test7_1_arg2  test7_1_arg3  test7_1_arg4))),
                    TestLabel "membership operation 2" (TestCase (assertEqual ((show test7_2_arg1) ++ (show test7_2_arg2) ++ (show test7_2_arg3)) test7_2_ans (membership test7_2_arg1 test7_2_arg2  test7_2_arg3  test7_2_arg4))),
                    TestLabel "membership operation 1" (TestCase (assertEqual ((show test7_3_arg1) ++ (show test7_3_arg2) ++ (show test7_3_arg3)) test7_3_ans (membership test7_3_arg1 test7_3_arg2  test7_3_arg3  test7_3_arg4))),
                    
                    TestLabel "PTBox 1" (TestCase (assertEqual ((show test8_1_arg)) test8_1_ans (ptboxToPConcept test8_1_arg))),
                    TestLabel "PTBox 2" (TestCase (assertEqual ((show test8_2_arg)) test8_2_ans (ptboxToPConcept test8_2_arg))),

                    TestLabel "AND 1(local)" (TestCase (assertEqual ((show test9_1_arg5)) test9_1_ans (reporting test9_1_arg1  test9_1_arg2 test9_1_arg3 test9_1_arg4 test9_1_arg5 ))),
                    TestLabel "AND 2(global inconsistent)" (TestCase (assertEqual ((show test9_2_arg5)) test9_2_ans (reporting test9_2_arg1  test9_2_arg2 test9_2_arg3 test9_2_arg4 test9_2_arg5 ))),
                    TestLabel "OR 1(local)" (TestCase (assertEqual ((show test9_3_arg5)) test9_3_ans (reporting test9_3_arg1  test9_3_arg2 test9_3_arg3 test9_3_arg4 test9_3_arg5 ))),
                    
                    TestLabel "AND OR GE (ori ex3.5-2)" (TestCase (assertEqual ((show test9_5_arg5)) test9_5_ans (reporting test9_5_arg1  test9_5_arg2 test9_5_arg3 test9_5_arg4 test9_5_arg5 ))),

                    TestLabel "AND OR GE (ori ex3.5-1 transitive)" (TestCase (assertEqual ((show test9_6_arg5)) test9_6_ans (reporting test9_6_arg1  test9_6_arg2 test9_6_arg3 test9_6_arg4 test9_6_arg5 ))),

                    TestLabel "AND OR GE  Satisfiable (ori ex3.5-1 transitive)" (TestCase (assertEqual ((show test10_1_arg1)) test10_1_ans (isSatisfiablePTBoxStatement test10_1_arg1 test10_1_arg2 test10_1_arg3)))
                 ]

unitTest = do runTestTT tests

