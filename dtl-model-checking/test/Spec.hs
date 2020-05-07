import           AutomataTheoreticApproach
--import qualified Data.Map.Lazy             as M
--import qualified Data.Set                  as S
import qualified DTLFormula                as F
--import qualified DTS                       as T
import           Test.Hspec
import ExampleInstances
import qualified BMC as B

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

    it "Testing for t8States2Agents1 and formula @_1[p1] => ~@_2[q1]" $
      modelCheck t8States2Agents1 (F.GNot (F.GImplies (F.Local 1 (F.PropositionalSymbol "p1")) (F.GNot $ F.Local 2 (F.PropositionalSymbol "q1")))) 2 `shouldBe` False

    it "Testing for t8States2Agents1 and formula @_2[X (c_1[p2])]" $
      modelCheck t8States2Agents1 (F.Local 2 (F.Next $ F.Comunicates 1 (F.PropositionalSymbol "p2"))) 2 `shouldBe` True
    it "testing for t8States2Agents4 and formula @_1[c_2[q_1]] => @_1[~p1=>p2]" $
      modelCheck t8States2Agents4 (F.GImplies (F.Local 1 (F.Comunicates 2 (F.PropositionalSymbol "q1"))) (F.Local 1 (F.Implies (F.Not $ F.PropositionalSymbol "p1") (F.PropositionalSymbol "p2")))) 2 `shouldBe` True

    it "testing for t8States2Agents4 and formula @_1[c_2[q_1]] => @_1[p1]" $
      modelCheck t8States2Agents4 (F.GImplies (F.Local 1 (F.Comunicates 2 (F.PropositionalSymbol "q1"))) (F.Local 1 (F.PropositionalSymbol "p1"))) 2 `shouldBe` False

    it "testing for t8States2Agents4 and formula @_1[c_2[q_1]] => @_1[p2]" $
      modelCheck t8States2Agents4 (F.GImplies (F.Local 1 (F.Comunicates 2 (F.PropositionalSymbol "q1"))) (F.Local 1 (F.PropositionalSymbol "p2"))) 2 `shouldBe` False

  -- Tests for bounded model checking --
  describe "Tests for bounded model checking - One agent" $ do
    it "Testing for @_1 [X p] and transition system oneAgent1" $
      B.modelCheck oneAgent1 (F.Local 1 (F.Next $ F.PropositionalSymbol "p")) 1 1 `shouldBe` False

    it "Testing for @_1  [p => ~p] and transition system oneAgent1" $
      B.modelCheck oneAgent1 (F.Local 1 (F.Implies (F.PropositionalSymbol "p") (F.Not $ F.PropositionalSymbol "p"))) 1 1 `shouldBe` False

    it "Testing for @_1  [p => p] and transition system oneAgent1" $
      B.modelCheck oneAgent1 (F.Local 1 (F.Implies (F.PropositionalSymbol "p") (F.PropositionalSymbol "p"))) 1 1 `shouldBe` True

    it "Testing for @_1[~p => Xp] and for transition system oneAgent1" $
      B.modelCheck oneAgent1 (F.Local 1 (F.Implies (F.Not $ F.PropositionalSymbol "p")(F.Next $ F.PropositionalSymbol "p"))) 1 5 `shouldBe` True

  describe "Tests for bounded model Checking - More than one agent" $ do
    it "Testing for @_1[X p], and the DTS in the thesis part of SAT" $
      B.modelCheck tThesis (F.Local 1 (F.Next $ F.PropositionalSymbol "p")) 2 1 `shouldBe` False

    it "Testing for @_1[c_2[~q]], and the transition system tThesis" $
      B.modelCheck tThesis (F.Local 1 (F.Comunicates 2 (F.Not $ F.PropositionalSymbol "q"))) 2 1 `shouldBe` False

    it "Testing for @_2[X X(c_1[p])], and the transition system tThesisComHolds" $
      -- we add the operator next because no communication formula is valid in an initial state --
      B.modelCheck tThesisComHolds (F.Local 2 (F.Next $ F.Next (F.Comunicates 1 (F.PropositionalSymbol "p")))) 2 1 `shouldBe` True

    it "Testing for @_2[X(c_1[p])], and the transition system tThesisComHolds" $
      -- we add the operator next because no communication formula is valid in an initial state --
      B.modelCheck tThesisComHolds (F.Local 2 (F.Next (F.Comunicates 1 (F.PropositionalSymbol "p")))) 2 1 `shouldBe` True

    it "Testing for @_1[p] => @_2[X(X q)] and for transition system tThesisNextNext" $
      B.modelCheck tThesisNextNextWitness (F.GImplies (F.Local 1 (F.PropositionalSymbol "p")) (F.Local 2 (F.Next (F.Next $ F.PropositionalSymbol "q")))) 2 4 `shouldBe` True

    it "Testing for @_1[F (p1 /\\ p2)] and transition system t8States2Agents4 with bound 0" $
      B.modelCheck t8States2Agents4 (F.Local 1 (F.Eventually (F.And (F.PropositionalSymbol "p1")(F.PropositionalSymbol "p2")))) 2 0 `shouldBe` True -- porque ainda nao foi encontrado nenhum loop

    it "Testing for @_1[F (p1 /\\ p2)] and transition system t8States2Agents4 with bound 1" $
      B.modelCheck t8States2Agents4 (F.Local 1 (F.Eventually (F.And (F.PropositionalSymbol "p1")(F.PropositionalSymbol "p2")))) 2 1 `shouldBe` False -- porque ja foi encontrado o loop 1-(3)^w

    it "Testing for @_1 [~p1 => F p1] and the transition system t8States2Agents with bound 10" $
      B.modelCheck t8States2Agents4 (F.Local 1 (F.Implies (F.Not $ F.PropositionalSymbol "p1") (F.Eventually $ F.PropositionalSymbol "p1"))) 2 10 `shouldBe` True

    it "Testing for @_1 [~p1 => F G p1] and the transition system t8States2Agents with bound 2" $
      B.modelCheck t8States2Agents4 (F.Local 1 (F.Implies (F.Not $ F.PropositionalSymbol "p1") (F.Eventually (F.Globally $ F.PropositionalSymbol "p1")))) 2 2 `shouldBe` True

    it "Testing for @_1 [~p1 => F G p1] and the transition system t8States2Agents with bound 3" $
      B.modelCheck t8States2Agents4 (F.Local 1 (F.Implies (F.Not $ F.PropositionalSymbol "p1") (F.Eventually (F.Globally $ F.PropositionalSymbol "p1")))) 2 3 `shouldBe` False

    it "Testing for @_1 [~p1 => G F p1] and the transition system t8States2Agents with bound 2" $
      B.modelCheck t8States2Agents4 (F.Local 1 (F.Implies (F.Not $ F.PropositionalSymbol "p1") (F.Globally (F.Eventually $ F.PropositionalSymbol "p1")))) 2 2 `shouldBe` True

    it "Testing for @_1 [~p1 => G F p1] and the transition system t8States2Agents with bound 10" $
      B.modelCheck t8States2Agents4 (F.Local 1 (F.Implies (F.Not $ F.PropositionalSymbol "p1") (F.Globally (F.Eventually $ F.PropositionalSymbol "p1")))) 2 10 `shouldBe` True

    it "Testing for @_1 [~p1 => G F X p1] and the transition system t8States2Agents with bound 10" $
      B.modelCheck t8States2Agents4 (F.Local 1 (F.Implies (F.Not $ F.PropositionalSymbol "p1") (F.Globally (F.Eventually (F.Next $ F.PropositionalSymbol "p1"))))) 2 10 `shouldBe` True

    it "Testing for t8States2Agents1 and formula @_2[X (c_1[p2])] and bound 2" $
      B.modelCheck t8States2Agents1 (F.Local 2 (F.Next $ F.Comunicates 1 (F.PropositionalSymbol "p2"))) 2 2 `shouldBe` True

    it "Testing for t8States2Agents1 and formula @_2[X (c_1[p2])] and bound 3" $
      B.modelCheck t8States2Agents1 (F.Local 2 (F.Next $ F.Comunicates 1 (F.PropositionalSymbol "p2"))) 2 3 `shouldBe` True

    it "Testing for t8States2Agents1 and formula @_2[X (c_1[p2])] and bound 4" $
      B.modelCheck t8States2Agents1 (F.Local 2 (F.Next $ F.Comunicates 1 (F.PropositionalSymbol "p2"))) 2 4 `shouldBe` True

    it "Testing for t8States2Agents1 and formula @_2[X (c_1[p2])] and bound 5" $
      B.modelCheck t8States2Agents1 (F.Local 2 (F.Next $ F.Comunicates 1 (F.PropositionalSymbol "p2"))) 2 5 `shouldBe` True

    it "Testing for t8States2Agents1 and formula @_2[X (c_1[p2])] and bound 6" $
      B.modelCheck t8States2Agents1 (F.Local 2 (F.Next $ F.Comunicates 1 (F.PropositionalSymbol "p2"))) 2 6 `shouldBe` True

    it "Testing for t8States2Agents1 and formula @_1 [F (p1 /\\ ~p2)] with bound 1" $
      B.modelCheck t8States2Agents1 (F.Local 1 (F.Eventually(F.And (F.PropositionalSymbol "p1") (F.Not $ F.PropositionalSymbol "p2")))) 2 1 `shouldBe` True

    it "Testing for t8States2Agents1 and formula @_1 [F (p1 /\\ ~p2)] with bound 2" $
      B.modelCheck t8States2Agents1 (F.Local 1 (F.Eventually(F.And (F.PropositionalSymbol "p1") (F.Not $ F.PropositionalSymbol "p2")))) 2 2 `shouldBe` False

    it "Testing for t8StatesAgents1 and formula @_1[(~p1/\\~p2) => X G ~(~p1 /\\ ~p1)] and bound 6" $
      B.modelCheck t8States2Agents1 (F.Local 1 (F.Implies (F.And (F.Not $ F.PropositionalSymbol "p1") (F.Not $ F.PropositionalSymbol "p2")) (F.Next $ F.Globally (F.Or (F.PropositionalSymbol"p1") (F.PropositionalSymbol "p2"))))) 2 6 `shouldBe` True

    it "Testing for t8State2Agents5 and formula @1_[X ((p2) \\/ (c_2[q1]))] and bound 1" $
      B.modelCheck  t8States2Agents5 (F.Local 1 (F.Next (F.Or (F.PropositionalSymbol "p2") (F.Comunicates 2 (F.PropositionalSymbol "q1"))))) 2 1 `shouldBe` False

    -- this witnesses the fact that the last action of two is not an action of 1
    it "Testing for t8States2Agents8 and formula @_2[X(c_1 [p1 \\/ ~p1])] and bound 3" $
      B.modelCheck  t8States2Agents8 (F.Local 2 (F.Next $ F.Comunicates 1 (F.Or (F.PropositionalSymbol "p1") (F.Not $ F.PropositionalSymbol "p1")))) 2 3 `shouldBe` False

    it "Testing for t8States2Agents8 and formula @_2[X(c_1 [p1 \\/ ~p1])] and bound 1" $
      B.modelCheck  t8States2Agents8 (F.Local 2 (F.Next $ F.Comunicates 1 (F.Or (F.PropositionalSymbol "p1") (F.Not $ F.PropositionalSymbol "p1")))) 2 1 `shouldBe` True

    -- this witnesses the fact that there loops were agent 2 never takes any action
    it "Testing for t8States2Agents4 and formula @_2[X(q1 \\/ ~q1)] and bound 1" $
      B.modelCheck t8States2Agents4 (F.Local 2 (F.Next $ F.Or (F.Not $ F.PropositionalSymbol "q1") (F.PropositionalSymbol "q1"))) 2 1 `shouldBe` False

    it "testing for t8States2Agents4 and formula @_1[c_2[q_1]] => @_1[p1] with bound 0" $
      B.modelCheck t8States2Agents4 (F.GImplies (F.Local 1 (F.Comunicates 2 (F.PropositionalSymbol "q1"))) (F.Local 1 (F.PropositionalSymbol "p1"))) 2 0 `shouldBe` True

    it "testing for t8States2Agents4 and formula @_1[c_2[q_1]] => @_1[p1] with bound 1" $
      B.modelCheck t8States2Agents4 (F.GImplies (F.Local 1 (F.Comunicates 2 (F.PropositionalSymbol "q1"))) (F.Local 1 (F.PropositionalSymbol "p1"))) 2 1 `shouldBe` True

    it "testing for t8States2Agents4 and formula @_1[c_2[q_1]] => @_1[p1] with bound 2" $
      B.modelCheck t8States2Agents4 (F.GImplies (F.Local 1 (F.Comunicates 2 (F.PropositionalSymbol "q1"))) (F.Local 1 (F.PropositionalSymbol "p1"))) 2 2 `shouldBe` True

    it "testing for t8States2Agents4 and formula @_1[c_2[q_1]] => @_1[p1] with bound 4" $
      B.modelCheck t8States2Agents4 (F.GImplies (F.Local 1 (F.Comunicates 2 (F.PropositionalSymbol "q1"))) (F.Local 1 (F.PropositionalSymbol "p1"))) 2 4 `shouldBe` False
