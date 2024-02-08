
# clear && make clean && make && ./test.sh 
echo "================="
echo "Test for bad"
for file in "./lattests/bad"/*
do
    if [[ $file == *.lat ]]; then
        echo "$file"
        ./latc_llvm "$file"
        echo ""
    fi
done

echo "================="
echo "Test for good"
for file in "./lattests/good"/*
do
    if [[ $file == *.lat ]]; then
        echo "$file"
        ./latc_llvm "$file"
        llvm_file="${file%.lat}.ll"
        bc_file="${file%.lat}.bc"  # replace .lat extension with .bc
        res_file="${file%.lat}.res"
        ans_file="${file%.lat}.output"
        lli "$bc_file" > "$res_file" # run lli on the .bc file to res_file
        if cmp -s "$res_file" "$ans_file"; then
            echo "Correct!"
            rm "$llvm_file" 
            rm "$res_file"
            rm "$bc_file"
        else
            echo "Wrong:"
            cat "$res_file"
            echo " vs "
            cat "$ans_file"
            exit
        fi
        echo ""
    fi
done

echo "================="
echo "Test for interactive"
for file in "./lattests/good_interactive"/*
do
    if [[ $file == *.lat ]]; then
        echo "$file"
        ./latc_llvm "$file"
        llvm_file="${file%.lat}.ll"
        bc_file="${file%.lat}.bc"
        res_file="${file%.lat}.res"
        ans_file="${file%.lat}.output"
        inp_file="${file%.lat}.input"
        cat "$inp_file" | lli "$bc_file" > "$res_file"
        if cmp -s "$res_file" "$ans_file"; then
            echo "Correct!"
            rm "$llvm_file" 
            rm "$res_file"
            rm "$bc_file"
        else
            echo "Wrong:"
            cat "$res_file"
            echo " vs "
            cat "$ans_file"
            exit
        fi
        echo ""
    fi
done

echo "================="
echo "Test for extensions"
for file in "./lattests/good_ext"/*
do
    if [[ $file == *.lat ]]; then
        echo "$file"
        ./latc_llvm "$file"
        llvm_file="${file%.lat}.ll"
        bc_file="${file%.lat}.bc"
        res_file="${file%.lat}.res"
        ans_file="${file%.lat}.output"
        lli "$bc_file" > "$res_file"
        if cmp -s "$res_file" "$ans_file"; then
            echo "Correct!"
            rm "$llvm_file" 
            rm "$res_file"
            rm "$bc_file"
        else
            echo "Wrong:"
            cat "$res_file"
            echo " vs "
            cat "$ans_file"
            exit
        fi
        echo ""
    fi
done

echo "================="
echo "Test for feedback cases"
for file in "./lattests/good_feedback"/*
do
    if [[ $file == *.lat ]]; then
        echo "$file"
        ./latc_llvm "$file"
        llvm_file="${file%.lat}.ll"
        bc_file="${file%.lat}.bc"
        res_file="${file%.lat}.res"
        ans_file="${file%.lat}.output"
        lli "$bc_file" > "$res_file"
        if cmp -s "$res_file" "$ans_file"; then
            echo "Correct!"
            rm "$llvm_file" 
            rm "$res_file"
            rm "$bc_file"
        else
            echo "Wrong:"
            cat "$res_file"
            echo " vs "
            cat "$ans_file"
            exit
        fi
        echo ""
    fi
done