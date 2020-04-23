import           AutomataTheoreticApproach
--import qualified Data.Map.Lazy             as M
--import qualified Data.Set                  as S
import qualified DTLFormula                as F
--import qualified DTS                       as T
import           Test.Hspec
import ExampleInstances

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

    it "Testing for @_2[X (c_1[p])], and the transition system tThesisComHolds" $
      -- we add the operator next because no communication formula is valid in an initial state --
      modelCheck tThesisComHolds (F.Local 2 (F.Next $ F.Next (F.Comunicates 1 (F.PropositionalSymbol "p")))) 2 `shouldBe` True

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

  -- some test instances on our random transition systems --
  describe "Test instances on \"randomly\" generated transition systems" $ do
    it "Testing for t8States2Agents1 and formula @_1[p1] /\\ @_2[q1]" $
      modelCheck t8States2Agents1 (F.GNot (F.GImplies (F.Local 1 (F.PropositionalSymbol "p1")) (F.GNot $ F.Local 2 (F.PropositionalSymbol "q1")))) 2 `shouldBe` False
    it "Testing for t8States2Agents1 and formula @_2[X (c_1[p2])]" $
      modelCheck t8States2Agents1 (F.Local 2 (F.Next $ F.Comunicates 1 (F.PropositionalSymbol "p2"))) 2 `shouldBe` True
    it "testing for t8States2Agents4 and formula @_1[c_2[q_1]] => @_1[~p1=>p2]" $
      modelCheck t8States2Agents4 (F.GImplies (F.Local 1 (F.Comunicates 2 (F.PropositionalSymbol "q1"))) (F.Local 1 (F.Implies (F.Not $ F.PropositionalSymbol "p1") (F.PropositionalSymbol "p2")))) 2 `shouldBe` True
    it "testing for t8States2Agents4 and formula @_1[c_2[q_1]] => @_1[p1]" $
      modelCheck t8States2Agents4 (F.GImplies (F.Local 1 (F.Comunicates 2 (F.PropositionalSymbol "q1"))) (F.Local 1 (F.PropositionalSymbol "p1"))) 2 `shouldBe` False
    it "testing for t8States2Agents4 and formula @_1[c_2[q_1]] => @_1[p2]" $
      modelCheck t8States2Agents4 (F.GImplies (F.Local 1 (F.Comunicates 2 (F.PropositionalSymbol "q1"))) (F.Local 1 (F.PropositionalSymbol "p2"))) 2 `shouldBe` False
