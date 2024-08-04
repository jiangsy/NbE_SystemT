Require nbe.systemt.intensional.totality.
Require nbe.systemt.extensional.soundness.
Require nbe.systemt.extensional.completeness.

Section Intensional.

    Import nbe.systemt.intensional.totality.

    Print Assumptions nbe.systemt.intensional.totality.nbe_totality.

End Intensional.


Section Extensional.

    Import nbe.systemt.extensional.soundness.
    Import nbe.systemt.extensional.completeness.

    Print Assumptions nbe.systemt.extensional.soundness.nbe_soundness.
    Print Assumptions nbe.systemt.extensional.soundness.nbe_totality.
    Print Assumptions nbe.systemt.extensional.completeness.nbe_completeness.
    Print Assumptions nbe.systemt.extensional.completeness.nbe_totality.
    
End Extensional.
