for i in *.dzn; do
	minizinc convert_data.mzn $i --soln-sep '' > ../$i
done
