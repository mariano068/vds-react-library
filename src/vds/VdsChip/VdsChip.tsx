import { ChipProps, IconButton, styled } from "@mui/material";
import * as React from "react";
import { IoIosClose } from "react-icons/io";
import { htmlToText } from "../../stories/utils";

const StyledChipContainer = styled('div')(() => ({
  fontSize: "12px",
  color: "#005075",
  letterSpacing: "0",
  lineHeight: "24px",
  fontFamily: "Cairo SemiBold",
  fontWeight: 600,
  textAlign: "left",
  padding: '0px 0px 0px 16px',
  borderRadius: '4px',
  backgroundColor: '#DEF0F7',
  display: 'flex',
  alignItems: 'center',
  margin: 2,
  width: 'max-content'
}));

const StyledIconButton = styled(IconButton)(() => ({
  padding: 0,
  color: "#005075 !important",
  fill: "#005075 !important",
  fontSize: "19.5px",
  letterSpacing: "0",
  textAlign: "center",
  fontWeight: 400,
  marginLeft: '5px',
  ':hover': {
    backgroundColor: 'unset',
    opacity: 'unset'
  }
}));

export const VdsChip = ({ label, onDelete, disabled }: ChipProps) => {

  return (
    <StyledChipContainer style={{ paddingRight: onDelete ? 0 : '16px' }}>
      {htmlToText(label)}
      {onDelete && (
        <StyledIconButton disabled={disabled} onClick={onDelete}>
          <IoIosClose />
        </StyledIconButton>
      )}
    </StyledChipContainer>
  );
}
