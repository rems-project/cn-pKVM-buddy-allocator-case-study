code=$(cloc --hide-rate --quiet --sum-one -csv --list-file source_code_file_list | awk 'END{print}' | awk -F "," '{print $NF}')

instr=$(cat source_code_file_list | xargs grep -E -- '\/\*CN\*\/' | wc -l | tr -d ' ')

spec=$(cat source_code_file_list | xargs grep -E -- '\/\*\@' | wc -l | tr -d ' ')


defs_cloc_output=$(cloc --hide-rate --quiet --sum-one -csv defs.h | awk 'END{print}')
lemmas_cloc_output=$(cloc --hide-rate --quiet --sum-one -csv lemmas.h | awk 'END{print}')

defs_code=$(echo $defs_cloc_output | awk -F "," '{print $NF}')
defs_comments=$(echo $defs_cloc_output | awk -F "," '{print $(NF-1)}')

lemmas_code=$(echo $lemmas_cloc_output | awk -F "," '{print $NF}')
lemmas_comments=$(echo $lemmas_cloc_output | awk -F "," '{print $(NF-1)}')


defs=$(($defs_code + $defs_comments))
lemma_stmnts=$(($lemmas_code + $lemmas_comments))

coq_proofs=$(cloc --hide-rate --quiet --sum-one -csv --list-file coq_proof_file_list | awk 'END{print}' | awk -F "," '{print $NF}')

formalisation=$(($instr + $spec + $defs + $lemma_stmnts + $coq_proofs))

overhead=$( echo "$formalisation / $code" | bc -l )

echo "Code: $code"
echo "Instr: $instr"
echo "Spec: $spec"
echo "Definitions: $defs"
echo "Lemma stmts: $lemma_stmnts"
echo "Coq proof: $coq_proofs"
echo "Formalisation total: $formalisation"
echo "Overhead: $overhead"
