Require nbe.common.list.

Require nbe.systemt.intensional.totality.
Require nbe.systemt.extensional.soundness.
Require nbe.systemt.extensional.completeness.

Section Intensional.

    Import nbe.systemt.intensional.totality.

    Check nbe.systemt.intensional.totality.nbe_totality.
    Print Assumptions nbe.systemt.intensional.totality.nbe_totality.

End Intensional.


Section Extensional.

    Import nbe.systemt.extensional.soundness.
    Import nbe.systemt.extensional.completeness.

    Check nbe.systemt.extensional.soundness.nbe_soundness.
    Print Assumptions nbe.systemt.extensional.soundness.nbe_soundness.
    Check nbe.systemt.extensional.soundness.nbe_totality.
    Print Assumptions nbe.systemt.extensional.soundness.nbe_totality.
    Check nbe.systemt.extensional.completeness.nbe_completeness.
    Print Assumptions nbe.systemt.extensional.completeness.nbe_completeness.
    Check nbe.systemt.extensional.completeness.nbe_totality.
    Print Assumptions nbe.systemt.extensional.completeness.nbe_totality.
    
End Extensional.
