import DAG.SearchCore

open DAG.SearchCore

namespace DAG

def sampleNames : Array String := #[
  "Test.Foo.alpha",
  "Test.Bar.beta",
  "DAG.SearchRank.searchEnv",
  "Socratic.Core"
]

example : containsCI "Test.Foo.alpha" "foo" = true := by
  native_decide

example : containsCI "Test.Foo.alpha" "zzz" = false := by
  native_decide

example :
    queryContains sampleNames "Test" =
      #["Test.Foo.alpha", "Test.Bar.beta"] := by
  native_decide

example :
    queryContainsCI sampleNames "test" =
      #["Test.Foo.alpha", "Test.Bar.beta"] := by
  native_decide

example : (queryContainsWithCount sampleNames "search").2 = 1 := by
  native_decide

example : (queryContainsWithCount sampleNames "missing").1 = #[] := by
  native_decide

end DAG
