import Baz.Baz

-- try evaluating an imported, ought-to-be precompiled constant
#eval barbaz
-- should not be precompiled (but we don't have a nice way to test either)
#eval bazbaz
