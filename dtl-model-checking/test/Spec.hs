import Test.Hspec
import AutomataTheoreticApproach
import qualified DTS as T
import qualified DTLFormula as F
import qualified Data.Map.Lazy as M
import qualified Data.Set as S

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
                                          ((1, "a"), [2]),
                                          ((1, "a"), [4]),
                                          ((1, "b"), [3]),
                                          ((2, "c"), [1]),
                                          ((3, "b"), [1]),
                                          ((4, "a"), [2])]}

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
