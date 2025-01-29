#!/usr/bin/fish
set i 0
for file in *
    echo "$i"
    set i (math $i + 1)
end
