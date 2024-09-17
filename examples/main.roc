app [main] {
    cli: platform "https://github.com/roc-lang/basic-cli/releases/download/0.15.0/SlwdbJ-3GR7uBWQo6zlmYWNYOxnvo8r6YABXD-45UOw.tar.br",
    kstrl: "../package/main.roc",
}

import cli.Stdout
import kstrl.Partial exposing [oneArity]

main : Task {} _
main =
    list2 = [1, 2, 3, 4, 5]
    list3 = ["a", "b", "c", "d", "e"]
    list4 = [1.1, 2.2, 3.3, 4.4, 5.5]

    strsWithStuff = 
        oneArity (ApplyLast (FromFive 
                List.map4
                list2 
                list3 
                list4
                \str1, int, str2, float -> "$(str1) + $(Num.toStr int)$(str2)$(Num.toStr float)"
            )
        )

    list1 = ["A", "B", "C", "D", "E"]
    Stdout.line! (Str.joinWith (strsWithStuff list1) "\n")