module [oneArity, twoArity, threeArity]

OneArity arg1 arg2 arg3 arg4 rem return : [
    ApplyFirst [
        FromTwo (arg1, rem -> return) arg1,
        FromThree (arg1, arg2, rem -> return) arg1 arg2,
        FromFour (arg1, arg2, arg3, rem -> return) arg1 arg2 arg3,
        FromFive (arg1, arg2, arg3, arg4, rem -> return) arg1 arg2 arg3 arg4,
    ],
    ApplyLast [
        FromTwo (rem, arg1 -> return) arg1,
        FromThree (rem, arg1, arg2 -> return) arg1 arg2,
        FromFour (rem, arg1, arg2, arg3 -> return) arg1 arg2 arg3,
        FromFive (rem, arg1, arg2, arg3, arg4 -> return) arg1 arg2 arg3 arg4,
    ]
]

TwoArity arg1 arg2 arg3 rem1 rem2 return : [
    ApplyFirst [
        FromThree (arg1, rem1, rem2 -> return) arg1,
        FromFour (arg1, arg2, rem1, rem2 -> return) arg1 arg2,
        FromFive (arg1, arg2, arg3, rem1, rem2 -> return) arg1 arg2 arg3,
    ],
    ApplyLast [
        FromThree (rem1, rem2, arg1 -> return) arg1,
        FromFour (rem1, rem2, arg1, arg2 -> return) arg1 arg2,
        FromFive (rem1, rem2, arg1, arg2, arg3 -> return) arg1 arg2 arg3,
    ]
]

ThreeArity arg1 arg2 rem1 rem2 rem3 return : [
    ApplyFirst [
        FromFour (arg1, rem1, rem2, rem3 -> return) arg1,
        FromFive (arg1, arg2, rem1, rem2, rem3 -> return) arg1 arg2,
    ],
    ApplyLast [
        FromFour (rem1, rem2, rem3, arg1 -> return) arg1,
        FromFive (rem1, rem2, rem3, arg1, arg2 -> return) arg1 arg2,
    ]
]

oneArity : OneArity arg1 arg2 arg3 arg4 rem return -> (rem -> return)
oneArity = \partial ->
    when partial is
        ApplyFirst (FromTwo func a1) -> 
            \r1 -> func a1 r1
        ApplyFirst (FromThree func a1 a2) -> 
            \r1 -> func a1 a2 r1
        ApplyFirst (FromFour func a1 a2 a3) -> 
            \r1 -> func a1 a2 a3 r1
        ApplyFirst (FromFive func a1 a2 a3 a4) ->
            \r1 -> func a1 a2 a3 a4 r1
        ApplyLast (FromTwo func a1) -> 
            \r1 -> func r1 a1
        ApplyLast (FromThree func a1 a2) ->
            \r1 -> func r1 a1 a2
        ApplyLast (FromFour func a1 a2 a3) ->
            \r1 -> func r1 a1 a2 a3
        ApplyLast (FromFive func a1 a2 a3 a4) ->
            \r1 -> func r1 a1 a2 a3 a4

twoArity : TwoArity arg1 arg2 arg3 rem1 rem2 return -> (rem1, rem2 -> return)
twoArity = \partial ->
    when partial is
        ApplyFirst (FromThree func a1) -> 
            \r1, r2 -> func a1 r1 r2
        ApplyFirst (FromFour func a1 a2) ->
            \r1, r2 -> func a1 a2 r1 r2
        ApplyFirst (FromFive func a1 a2 a3) ->
            \r1, r2 -> func a1 a2 a3 r1 r2
        ApplyLast (FromThree func a1) ->
            \r1, r2 -> func r1 r2 a1
        ApplyLast (FromFour func a1 a2) ->
            \r1, r2 -> func r1 r2 a1 a2
        ApplyLast (FromFive func a1 a2 a3) ->
            \r1, r2 -> func r1 r2 a1 a2 a3

threeArity : ThreeArity arg1 arg2 rem1 rem2 rem3 return -> (rem1, rem2, rem3 -> return)
threeArity =\partial ->
    when partial is
        ApplyFirst (FromFour func a1) ->
            \r1, r2, r3 -> func a1 r1 r2 r3
        ApplyFirst (FromFive func a1 a2) ->
            \r1, r2, r3 -> func a1 a2 r1 r2 r3
        ApplyLast (FromFour func a1) ->
            \r1, r2, r3 -> func r1 r2 r3 a1
        ApplyLast (FromFive func a1 a2) ->
            \r1, r2, r3 -> func r1 r2 r3 a1 a2


expect
    # TEST: reduction from four arity
    catFour = \s1, s2, s3, s4 -> "$(s1)$(s2)$(s3)$(s4)"
    abcAnd = oneArity (ApplyFirst (FromFour catFour "a" "b" "c"))
    bcdPrep = oneArity (ApplyLast (FromFour catFour "b" "c" "d"))
    abAnd = twoArity (ApplyFirst (FromFour catFour "a" "b"))
    dcPrep = twoArity (ApplyLast (FromFour catFour "c" "d"))
    aAnd = threeArity (ApplyFirst (FromFour catFour "a"))
    dPrep = threeArity (ApplyLast (FromFour catFour "d"))
    (abcAnd "d" == "abcd")
    && (bcdPrep "a" == "abcd")
    && (abAnd "c" "d" == "abcd")
    && (dcPrep "a" "b" == "abcd")
    && (aAnd "b" "c" "d" == "abcd")
    && (dPrep "a" "b" "c" == "abcd")
    
expect
    # TEST: reduction from three arity
    catThree = \s1, s2, s3 -> "$(s1)$(s2)$(s3)"
    abAnd = oneArity (ApplyFirst (FromThree catThree "a" "b"))
    bcPrep = oneArity (ApplyLast (FromThree catThree "b" "c"))
    aAnd = twoArity (ApplyFirst (FromThree catThree "a"))
    cPrep = twoArity (ApplyLast (FromThree catThree "c"))
    (abAnd "c" == "abc")
    && (bcPrep "a" == "abc")
    && (aAnd "b" "c" == "abc")
    && (cPrep "a" "b" == "abc")

expect
    # TEST: reduction from two arity
    catTwo = \s1, s2 -> "$(s1)$(s2)"
    aAnd = oneArity (ApplyFirst (FromTwo catTwo "a"))
    bPrep = oneArity (ApplyLast (FromTwo catTwo "b"))
    (aAnd "b" == "ab")
    && (bPrep "a" == "ab")