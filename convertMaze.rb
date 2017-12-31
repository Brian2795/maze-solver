#!/usr/bin/ruby

fail "usage: convertMaze.rb <filename>" if ARGV.length != 1

maze_file = open(ARGV[0])
lines = maze_file.readlines

# 1st line must be maze header
line = lines.shift
sz, sx, sy, ex, ey = line.split(/\s/)
puts "maze(#{sz},#{sx},#{sy},#{ex},#{ey})."

lines.each { |line|
    # begins with "path", must be path specification
    if line[0...4] == "path"
       p, name, x, y, ds = line.split(/\s/)
       d = ds.split("").join(",")
       puts "path('#{name}',#{x},#{y},[#{d}])."

    # otherwise must be cell specification (since maze spec must be valid)
    else
       x, y, ds, w = line.split(/\s/,4)
       d = ds.split("").join(",")
       ws = w.split(/\s/).join(",")
       puts "cell(#{x},#{y},[#{d}],[#{ws}])."
    end
}
