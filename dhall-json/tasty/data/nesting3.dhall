let Example = < Left : { foo : Natural } | Middle | Right : { bar : Bool } >

let Nesting = < Inline | Nested : Text >

in  { field    = "name"
    , nesting  = Nesting.Nested "value"
    , contents = Example.Middle
    }
