#!/usr/bin/env ruby

# Slow list version
def apply_day(fish)
    fish.map { |f| f == 0 ? 6 : f - 1 }
end

def new_fish(fish)
    fish.reduce([]) { |new, f| f == 0 ? [8] + new : new }
end

def apply_days(fish, days)
    days.times do
        fish = new_fish(fish) + apply_day(fish)
    end

    puts fish.count
end

# Indexed version
def apply_day_index!(fish_index)
    curr_zeros = fish_index[0]
    1.upto(8).each do |i|
        prev_i = i - 1
        fish_index[prev_i] += fish_index[i]
        fish_index[i] -= fish_index[i]
    end
    fish_index[8] += curr_zeros
    fish_index[6] += curr_zeros
    fish_index[0] -= curr_zeros
end

def apply_days_index(fish_index, days)
    days.times do
        puts "--- Before ---"
        puts fish_index
        puts
        apply_day_index!(fish_index)
    end
end

fish = [4,1,4,1,3,3,1,4,3,3,2,1,1,3,5,1,3,5,2,5,1,5,5,1,3,2,5,3,1,3,4,2,3,2,3,3,2,1,5,4,1,1,1,2,1,4,4,4,2,1,2,1,5,1,5,1,2,1,4,4,5,3,3,4,1,4,4,2,1,4,4,3,5,2,5,4,1,5,1,1,1,4,5,3,4,3,4,2,2,2,2,4,5,3,5,2,4,2,3,4,1,4,4,1,4,5,3,4,2,2,2,4,3,3,3,3,4,2,1,2,5,5,3,2,3,5,5,5,4,4,5,5,4,3,4,1,5,1,3,4,4,1,3,1,3,1,1,2,4,5,3,1,2,4,3,3,5,4,4,5,4,1,3,1,1,4,4,4,4,3,4,3,1,4,5,1,2,4,3,5,1,1,2,1,1,5,4,2,1,5,4,5,2,4,4,1,5,2,2,5,3,3,2,3,1,5,5,5,4,3,1,1,5,1,4,5,2,1,3,1,2,4,4,1,1,2,5,3,1,5,2,4,5,1,2,3,1,2,2,1,2,2,1,4,1,3,4,2,1,1,5,4,1,5,4,4,3,1,3,3,1,1,3,3,4,2,3,4,2,3,1,4,1,5,3,1,1,5,3,2,3,5,1,3,1,1,3,5,1,5,1,1,3,1,1,1,1,3,3,1]
small_fish = [3,4,3,1,2]

initial = fish

index = {}
0.upto(8).each { |i| index[i] = 0 }
index_fish = initial.group_by { |i| i }.transform_values { |f| f.count }
index.merge!(index_fish)

apply_days_index(index, 256)

count = 0
index.each { |_, c| count += c }
puts count
# apply_days small_fish, 256

