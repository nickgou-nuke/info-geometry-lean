import DAG.SearchCore

open DAG.SearchCore

namespace DAG

def sampleNames : Array String := #[
  "Test.Foo.alpha",
  "Test.Bar.beta",
  "DAG.SearchRank.searchEnv",
  "Socratic.Core"
]

example : containsCI "Test.Foo.alpha" "foo" = true := by decide

example : containsCI "Test.Foo.alpha" "zzz" = false := by decide

example :
    queryContains sampleNames "Test" =
      #["Test.Foo.alpha", "Test.Bar.beta"] := by decide

example :
    queryContainsCI sampleNames "test" =
      #["Test.Foo.alpha", "Test.Bar.beta"] := by decide

example : (queryContainsWithCount sampleNames "search").2 = 1 := by decide

example : (queryContainsWithCount sampleNames "missing").1 = #[] := by decide

end DAG
