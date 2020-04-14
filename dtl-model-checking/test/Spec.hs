import           AutomataTheoreticApproach
import qualified Data.Map.Lazy             as M
import qualified Data.Set                  as S
import qualified DTLFormula                as F
import qualified DTS                       as T
import           Test.Hspec

tThesis = T.DTS {T.states = S.fromList [1, 2, 3, 4] :: S.Set Int,
        T.actions = M.fromList [(1::Int, S.fromList ["a", "b"]), (2, S.fromList ["a", "c"])],
        T.initialStates = S.fromList [1, 4],
        T.propSymbols = M.fromList [
            (1, S.fromList [F.FromLocal $ F.PropositionalSymbol "p"]),
            (2, S.fromList [F.FromLocal $ F.PropositionalSymbol "q"])
                    ],
        T.labelingFunction = M.fromList [
                                      ((1, 1), S.fromList [F.FromLocal $ F.PropositionalSymbol "p"]),
                                      ((1, 2), S.fromList [F.FromLocal $ F.PropositionalSymbol "q"]),
                                      ((2, 1), S.fromList [F.FromLocal $ F.PropositionalSymbol "p"]),
                                      ((2, 2), S.fromList []),
                                      ((3, 1), S.fromList []),
                                      ((3, 2), S.fromList [F.FromLocal $ F.PropositionalSymbol "q"]),
                                      ((4, 1), S.fromList []),
                                      ((4, 2), S.fromList [])
                                      ],
        T.transitionRelation = M.fromList [
                                          ((1, "a"), [2, 4]),
                                          ((1, "b"), [3]),
                                          ((2, "c"), [1]),
                                          ((3, "b"), [1]),
                                          ((4, "a"), [2])]}


-- A witness for @_1[p] => @_2[X(X p)]. This is achieved by removing the 4th
-- state from tThesis and removing p from the second state.
-- NOTE: This still is not enough for the formula to hold. We need to remove the third state
--       otherwise we will just stay in a 1-3-1-3-1-3-1-3 forever without witnessing
--       the satisfaction of XXp
tThesisNextNext = T.DTS {T.states = S.fromList [1, 2, 3] :: S.Set Int,
        T.actions = M.fromList [(1::Int, S.fromList ["a", "b"]), (2, S.fromList ["a", "c"])],
        T.initialStates = S.fromList [1],
        T.propSymbols = M.fromList [
            (1, S.fromList [F.FromLocal $ F.PropositionalSymbol "p"]),
            (2, S.fromList [F.FromLocal $ F.PropositionalSymbol "q"])
                    ],
        T.labelingFunction = M.fromList [
                                      ((1, 1), S.fromList [F.FromLocal $ F.PropositionalSymbol "p"]),
                                      ((1, 2), S.fromList [F.FromLocal $ F.PropositionalSymbol "q"]),
                                      ((2, 1), S.fromList []),
                                      ((2, 2), S.fromList []),
                                      ((3, 1), S.fromList []),
                                      ((3, 2), S.fromList [F.FromLocal $ F.PropositionalSymbol "q"])
                                      ],
        T.transitionRelation = M.fromList [
                                          ((1, "a"), [2]),
                                          ((1, "b"), [3]),
                                          ((2, "c"), [1]),
                                          ((3, "b"), [1])]}


-- The final witness for @_1[p] => @_2[XXp]
tThesisNextNextWitness = T.deleteStates tThesisNextNext [3]


-- A witness for "@_2[]c_1(p)"
tThesisComHolds = T.DTS {T.states = S.fromList [1, 2] :: S.Set Int,
        T.actions = M.fromList [(1::Int, S.fromList ["a", "b"]), (2, S.fromList ["b"])],
        T.initialStates = S.fromList [1],
        T.propSymbols = M.fromList [
            (1, S.fromList [F.FromLocal $ F.PropositionalSymbol "p"]),
            (2, S.fromList [F.FromLocal $ F.PropositionalSymbol "q"])
                    ],
        T.labelingFunction = M.fromList [
                                      ((1, 1), S.fromList [F.FromLocal $ F.PropositionalSymbol "p"]),
                                      ((1, 2), S.fromList [F.FromLocal $ F.PropositionalSymbol "q"]),
                                      ((2, 1), S.fromList []),
                                      ((2, 2), S.fromList [])
                                      ],
        T.transitionRelation = M.fromList [
                                          ((1, "a"), [2]),
                                          ((2, "b"), [1])]}


oneAgent1 = T.DTS {T.states = S.fromList [1, 2] :: S.Set Int,
                   T.initialStates = S.fromList [1] :: S.Set Int,
                   T.actions = M.fromList [(1::Int, S.fromList ["a"])],
                   T.propSymbols = M.fromList [
                      (1, S.fromList [F.FromLocal $ F.PropositionalSymbol "p"])],
                   T.labelingFunction = M.fromList[
                      ((1, 1), S.fromList [F.FromLocal $ F.PropositionalSymbol "p"]),
                      ((2, 1), S.fromList [])],
                   T.transitionRelation = M.fromList[
                      ((1, "a"), [2]),
                      ((2, "a"), [1])]}

main :: IO()
main = hspec $ do
  describe "Tests for one agent. Easier to see what is going on, Basically LTL" $ do
    it "Testing for @_1 [X p] and transition system oneAgent1" $
      modelCheck oneAgent1 (F.Local 1 (F.Next $ F.PropositionalSymbol "p")) 1 `shouldBe` False

    it "Testing for @_1  [p => ~p] and transition system oneAgent1" $
      modelCheck oneAgent1 (F.Local 1 (F.Implies (F.PropositionalSymbol "p") (F.Not $ F.PropositionalSymbol "p"))) 1 `shouldBe` False

    it "Testing for @_1  [p => p] and transition system oneAgent1" $
      modelCheck oneAgent1 (F.Local 1 (F.Implies (F.PropositionalSymbol "p") (F.PropositionalSymbol "p"))) 1 `shouldBe` True

    it "Testing for @_1[F p] = @_1 [~G ~p] and for transition system oneAgent1" $
      modelCheck oneAgent1 (F.Local 1 (F.Not(F.Globally(F.Not $ F.PropositionalSymbol "p")))) 1 `shouldBe` True

    it "Testing for @_1[~p => Xp] and for transition system oneAgent1" $
      modelCheck oneAgent1 (F.Local 1 (F.Implies (F.Not $ F.PropositionalSymbol "p")(F.Next $ F.PropositionalSymbol "p"))) 1 `shouldBe` True

    it "Testing for @_1[G (~p => Xp)] and for transition system oneAgent1" $
      modelCheck oneAgent1 (F.Local 1 (F.Globally $ F.Implies (F.Not $ F.PropositionalSymbol "p")(F.Next $ F.PropositionalSymbol "p"))) 1 `shouldBe` True

    it "Testing for @_1 [p] and for transtion system oneAgent1" $
      modelCheck oneAgent1 (F.Local 1 (F.PropositionalSymbol "p")) 1 `shouldBe` False

    it "Testing for @_1[G p] and for transition system oneAgent1" $
      modelCheck oneAgent1 (F.Local 1 (F.Globally $ F.PropositionalSymbol "p")) 1 `shouldBe` False


  -- Here we begin the test for more than one agent --
  describe "Tests for more than one agent" $ do
    it "Testing for @_1[X p], and the DTS in the thesis part of SAT" $
      modelCheck tThesis (F.Local 1 (F.Next $ F.PropositionalSymbol "p")) 2 `shouldBe` False

    it "Testing for @_1[c_2[~q]], and the transition system tThesis" $
      modelCheck tThesis (F.Local 1 (F.Comunicates 2 (F.Not $ F.PropositionalSymbol "q"))) 2 `shouldBe` False

    it "Testing for @_1[c_2[~q]], and the transition system tThesisComHolds" $
      modelCheck tThesis (F.Local 1 (F.Comunicates 2 (F.Not $ F.PropositionalSymbol "q"))) 2 `shouldBe` False

    it "Testing for @_2[c_1[p]], and the transition system tThesisComHolds" $
      modelCheck tThesisComHolds (F.Local 2 (F.Comunicates 1 (F.PropositionalSymbol "p"))) 2 `shouldBe` True

    it "Testing for @_1[p] => @_2[F q] and for transition system in thesis" $
      modelCheck tThesis (F.GImplies (F.Local 1 (F.PropositionalSymbol "p")) (F.Local 2 (F.Not(F.Globally(F.Not $ F.PropositionalSymbol "q"))))) 2 `shouldBe` True

    it "Testing for @_1[p] => @_2[X q] and for transition system tThesis" $
      modelCheck tThesis (F.GImplies (F.Local 1 (F.PropositionalSymbol "p")) (F.Local 2 (F.Next $ F.PropositionalSymbol "q"))) 2 `shouldBe` False

    it "Testing for @_1[p] => @_2[X(X q)] and for transition system tThesis" $
      modelCheck tThesis (F.GImplies (F.Local 1 (F.PropositionalSymbol "p")) (F.Local 2 (F.Next (F.Next $ F.PropositionalSymbol "q")))) 2 `shouldBe` False -- because 1a4a2

    it "Testing for @_1[p] => @_2[X(X q)] and for transition system tThesisNextNext" $
      modelCheck tThesisNextNext (F.GImplies (F.Local 1 (F.PropositionalSymbol "p")) (F.Local 2 (F.Next (F.Next $ F.PropositionalSymbol "q")))) 2 `shouldBe` False

    it "Testing for @_1[p] => @_2[X(X q)] and for transition system tThesisNextNext" $
      modelCheck tThesisNextNextWitness (F.GImplies (F.Local 1 (F.PropositionalSymbol "p")) (F.Local 2 (F.Next (F.Next $ F.PropositionalSymbol "q")))) 2 `shouldBe` True
