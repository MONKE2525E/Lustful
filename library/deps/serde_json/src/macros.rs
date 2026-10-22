// Adapted from serde_json 1.0.151 src/macros.rs under the MIT license.
// See ../LICENSE-MIT. Expression fragments retain upstream edition-2021 grammar.
#[macro_export]
macro_rules! json {
    // Hide distracting implementation details from the generated rustdoc.
    ($($json:tt)+) => {
        $crate::json_internal!($($json)+)
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! json_internal {
    //////////////////////////////////////////////////////////////////////////
    // TT muncher for parsing the inside of an array [...]. Produces a vec![...]
    // of the elements.
    //
    // Must be invoked as: json_internal!(@array [] $($tt)*)
    //////////////////////////////////////////////////////////////////////////

    // Done with trailing comma.
    (@array [$($elems:expr_2021,)*]) => {
        ::std::vec![$($elems,)*]
    };

    // Done without trailing comma.
    (@array [$($elems:expr_2021),*]) => {
        ::std::vec![$($elems),*]
    };

    // Next element is `null`.
    (@array [$($elems:expr_2021,)*] null $($rest:tt)*) => {
        $crate::json_internal!(@array [$($elems,)* $crate::json_internal!(null)] $($rest)*)
    };

    // Next element is `true`.
    (@array [$($elems:expr_2021,)*] true $($rest:tt)*) => {
        $crate::json_internal!(@array [$($elems,)* $crate::json_internal!(true)] $($rest)*)
    };

    // Next element is `false`.
    (@array [$($elems:expr_2021,)*] false $($rest:tt)*) => {
        $crate::json_internal!(@array [$($elems,)* $crate::json_internal!(false)] $($rest)*)
    };

    // Next element is an array.
    (@array [$($elems:expr_2021,)*] [$($array:tt)*] $($rest:tt)*) => {
        $crate::json_internal!(@array [$($elems,)* $crate::json_internal!([$($array)*])] $($rest)*)
    };

    // Next element is a map.
    (@array [$($elems:expr_2021,)*] {$($map:tt)*} $($rest:tt)*) => {
        $crate::json_internal!(@array [$($elems,)* $crate::json_internal!({$($map)*})] $($rest)*)
    };

    // Next element is an expression followed by comma.
    (@array [$($elems:expr_2021,)*] $next:expr_2021, $($rest:tt)*) => {
        $crate::json_internal!(@array [$($elems,)* $crate::json_internal!($next),] $($rest)*)
    };

    // Last element is an expression with no trailing comma.
    (@array [$($elems:expr_2021,)*] $last:expr_2021) => {
        $crate::json_internal!(@array [$($elems,)* $crate::json_internal!($last)])
    };

    // Comma after the most recent element.
    (@array [$($elems:expr_2021),*] , $($rest:tt)*) => {
        $crate::json_internal!(@array [$($elems,)*] $($rest)*)
    };

    // Unexpected token after most recent element.
    (@array [$($elems:expr_2021),*] $unexpected:tt $($rest:tt)*) => {
        $crate::json_unexpected!($unexpected)
    };

    //////////////////////////////////////////////////////////////////////////
    // TT muncher for parsing the inside of an object {...}. Each entry is
    // inserted into the given map variable.
    //
    // Must be invoked as: json_internal!(@object $map () ($($tt)*) ($($tt)*))
    //
    // We require two copies of the input tokens so that we can match on one
    // copy and trigger errors on the other copy.
    //////////////////////////////////////////////////////////////////////////

    // Done.
    (@object $object:ident () () ()) => {};

    // Insert the current entry followed by trailing comma.
    (@object $object:ident [$($key:tt)+] ($value:expr_2021) , $($rest:tt)*) => {
        let _ = $object.insert(($($key)+).into(), $value);
        $crate::json_internal!(@object $object () ($($rest)*) ($($rest)*));
    };

    // Current entry followed by unexpected token.
    (@object $object:ident [$($key:tt)+] ($value:expr_2021) $unexpected:tt $($rest:tt)*) => {
        $crate::json_unexpected!($unexpected);
    };

    // Insert the last entry without trailing comma.
    (@object $object:ident [$($key:tt)+] ($value:expr_2021)) => {
        let _ = $object.insert(($($key)+).into(), $value);
    };

    // Next value is `null`.
    (@object $object:ident ($($key:tt)+) (: null $($rest:tt)*) $copy:tt) => {
        $crate::json_internal!(@object $object [$($key)+] ($crate::json_internal!(null)) $($rest)*);
    };

    // Next value is `true`.
    (@object $object:ident ($($key:tt)+) (: true $($rest:tt)*) $copy:tt) => {
        $crate::json_internal!(@object $object [$($key)+] ($crate::json_internal!(true)) $($rest)*);
    };

    // Next value is `false`.
    (@object $object:ident ($($key:tt)+) (: false $($rest:tt)*) $copy:tt) => {
        $crate::json_internal!(@object $object [$($key)+] ($crate::json_internal!(false)) $($rest)*);
    };

    // Next value is an array.
    (@object $object:ident ($($key:tt)+) (: [$($array:tt)*] $($rest:tt)*) $copy:tt) => {
        $crate::json_internal!(@object $object [$($key)+] ($crate::json_internal!([$($array)*])) $($rest)*);
    };

    // Next value is a map.
    (@object $object:ident ($($key:tt)+) (: {$($map:tt)*} $($rest:tt)*) $copy:tt) => {
        $crate::json_internal!(@object $object [$($key)+] ($crate::json_internal!({$($map)*})) $($rest)*);
    };

    // Next value is an expression followed by comma.
    (@object $object:ident ($($key:tt)+) (: $value:expr_2021 , $($rest:tt)*) $copy:tt) => {
        $crate::json_internal!(@object $object [$($key)+] ($crate::json_internal!($value)) , $($rest)*);
    };

    // Last value is an expression with no trailing comma.
    (@object $object:ident ($($key:tt)+) (: $value:expr_2021) $copy:tt) => {
        $crate::json_internal!(@object $object [$($key)+] ($crate::json_internal!($value)));
    };

    // Missing value for last entry. Trigger a reasonable error message.
    (@object $object:ident ($($key:tt)+) (:) $copy:tt) => {
        // "unexpected end of macro invocation"
        $crate::json_internal!();
    };

    // Missing colon and value for last entry. Trigger a reasonable error
    // message.
    (@object $object:ident ($($key:tt)+) () $copy:tt) => {
        // "unexpected end of macro invocation"
        $crate::json_internal!();
    };

    // Misplaced colon. Trigger a reasonable error message.
    (@object $object:ident () (: $($rest:tt)*) ($colon:tt $($copy:tt)*)) => {
        // Takes no arguments so "no rules expected the token `:`".
        $crate::json_unexpected!($colon);
    };

    // Found a comma inside a key. Trigger a reasonable error message.
    (@object $object:ident ($($key:tt)*) (, $($rest:tt)*) ($comma:tt $($copy:tt)*)) => {
        // Takes no arguments so "no rules expected the token `,`".
        $crate::json_unexpected!($comma);
    };

    // Key is fully parenthesized. This avoids clippy double_parens false
    // positives because the parenthesization may be necessary here.
    (@object $object:ident () (($key:expr_2021) : $($rest:tt)*) $copy:tt) => {
        $crate::json_internal!(@object $object ($key) (: $($rest)*) (: $($rest)*));
    };

    // Refuse to absorb colon token into key expression.
    (@object $object:ident ($($key:tt)*) (: $($unexpected:tt)+) $copy:tt) => {
        $crate::json_expect_expr_comma!($($unexpected)+);
    };

    // Munch a token into the current key.
    (@object $object:ident ($($key:tt)*) ($tt:tt $($rest:tt)*) $copy:tt) => {
        $crate::json_internal!(@object $object ($($key)* $tt) ($($rest)*) ($($rest)*));
    };

    //////////////////////////////////////////////////////////////////////////
    // The main implementation.
    //
    // Must be invoked as: json_internal!($($json)+)
    //////////////////////////////////////////////////////////////////////////

    (null) => {
        $crate::Value::Null
    };

    (true) => {
        $crate::Value::Bool(true)
    };

    (false) => {
        $crate::Value::Bool(false)
    };

    ([]) => {
        $crate::Value::Array(::std::vec![])
    };

    ([ $($tt:tt)+ ]) => {
        $crate::Value::Array($crate::json_internal!(@array [] $($tt)+))
    };

    ({}) => {
        $crate::Value::Object($crate::Map::new())
    };

    ({ $($tt:tt)+ }) => {
        $crate::Value::Object({
            let mut object = $crate::Map::new();
            $crate::json_internal!(@object object () ($($tt)+) ($($tt)+));
            object
        })
    };

    // Only expressions whose types implement the sealed JsonInput bound.
    // Must be below every other rule.
    ($other:expr_2021) => {
        $crate::to_value(&$other).unwrap()
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! json_unexpected {
    () => {};
}

#[macro_export]
#[doc(hidden)]
macro_rules! json_expect_expr_comma {
    ($e:expr_2021 , $($tt:tt)*) => {};
}
