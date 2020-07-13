import           DTS                       as T
import           ExampleInstances

main :: IO()
main =
  do writeFile "t8States1" (T.dumpToString $ T.fullSimplify t8States2Agents1)
     writeFile "t8States2" (T.dumpToString $ T.fullSimplify t8States2Agents2)
     writeFile "t8States3" (T.dumpToString $ T.fullSimplify t8States2Agents3)
     writeFile "t8States4" (T.dumpToString $ T.fullSimplify t8States2Agents4)

     writeFile "t16States1" (T.dumpToString $ T.fullSimplify t16States2Agents1)
     writeFile "t16States2" (T.dumpToString $ T.fullSimplify t16States2Agents2)
     writeFile "t16States3" (T.dumpToString $ T.fullSimplify t16States2Agents3)
     writeFile "t16States4" (T.dumpToString $ T.fullSimplify t16States2Agents4)

     writeFile "t32States1" (T.dumpToString $ T.fullSimplify t32States2Agents1)
     writeFile "t32States2" (T.dumpToString $ T.fullSimplify t32States2Agents2)
     writeFile "t32States3" (T.dumpToString $ T.fullSimplify t32States2Agents3)
     writeFile "t32States4" (T.dumpToString $ T.fullSimplify t32States2Agents4)

     writeFile "t64States1" (T.dumpToString $ T.fullSimplify t64States2Agents1)
     writeFile "t64States2" (T.dumpToString $ T.fullSimplify t64States2Agents2)

     writeFile "t128States1" (T.dumpToString $ T.fullSimplify t128States2Agents1)
     writeFile "t128States2" (T.dumpToString $ T.fullSimplify t128States2Agents2)

     writeFile "t256States1" (T.dumpToString $ T.fullSimplify t256States2Agents1)
     writeFile "t256States2" (T.dumpToString $ T.fullSimplify t256States2Agents2)

     writeFile "t512States1" (T.dumpToString $ T.fullSimplify t512States2Agents1)
     writeFile "t512States2" (T.dumpToString $ T.fullSimplify t512States2Agents2)

     writeFile "t1024States1" (T.dumpToString $ T.fullSimplify t1024States2Agents1)
     writeFile "t1024States2" (T.dumpToString $ T.fullSimplify t1024States2Agents2)
