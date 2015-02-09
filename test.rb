#!/usr/bin/ruby
#
#Colored output. This won't work in Windows.
class String
  def green() "\x1B[32m#{self}\x1B[0m" end
  def red()   "\x1B[31m#{self}\x1B[0m" end
end

passed, total = [0, 0]
Dir["test/*v"].each do |vfile|
  name = vfile.sub(/\.v/, '').sub(/test\//, '')
  expected = File.open("test/#{name}.expected",'r').read
  actual   = %x[iverilog -z #{vfile} && z3 -smt2 #{name}.z3]
  total +=1
  if actual == expected
    puts "PASSED #{name}".green
    passed += 1
  else
    puts "FAILED #{name}".red
    puts expected.green
    puts actual.red
  end
end

%x[rm *z3]
puts "Passed #{passed}/#{total} tests"
