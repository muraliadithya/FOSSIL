$files = Get-ChildItem "C:\Users\hrish\OneDrive\Documents\GitHub\FOSSIL\vcgen\verifiedEqSp\all"

Write-Output "(-----------Now starting FL-------)";
foreach ($f in $files){
    # $outfile = $f.FullName + "out" 
    # Get-Content $f.FullName | Where-Object { ($_ -match 'step4' -or $_ -match 'step9') } | Set-Content $outfile
        $f_path = "C:\Users\hrish\OneDrive\Documents\GitHub\FOSSIL\vcgen\verifiedEqSp\all\$f"
        $m = Measure-Command{python C:\Users\hrish\OneDrive\Documents\GitHub\FOSSIL\vcgen\runbench.py $f_path --lang fl --mode 4 --one-vc}
        Write-Output "($f,   $m)";
        # python runbench.py benchmarksSL/sll/sll_append.fsl --lang sl --mode 4 --one-vc
}



$files = Get-ChildItem "C:\Users\hrish\OneDrive\Documents\GitHub\FOSSIL\vcgen\benchmarksSL\all"

Write-Output "(-----------Now starting SL-------)";
foreach ($f in $files){
    # $outfile = $f.FullName + "out" 
    # Get-Content $f.FullName | Where-Object { ($_ -match 'step4' -or $_ -match 'step9') } | Set-Content $outfile
        $f_path = "C:\Users\hrish\OneDrive\Documents\GitHub\FOSSIL\vcgen\benchmarksSL\all\$f"
        $m = Measure-Command{python C:\Users\hrish\OneDrive\Documents\GitHub\FOSSIL\vcgen\runbench.py $f_path --lang sl --mode 4 --one-vc}
        Write-Output "($f,   $m)";
        # python runbench.py benchmarksSL/sll/sll_append.fsl --lang sl --mode 4 --one-vc
}