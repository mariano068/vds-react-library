import { Link, Typography } from '@mui/material'
import * as React from 'react'
import { Highlight } from '../shared/Highlight'
import { VdsBreadcrumb } from '../../vds/VdsBreadcrumb/VdsBreadcrumb'
import { VdsPageTitle } from '../../vds/VdsPageTitle/VdsPageTitle'
import { convert } from '../utils'
import CodeHighlight from '../shared/CodeHighlight'

//#region Snippets
export const breadcrumb_snippet = convert(`
import React from 'react';
import { Breadcrumb } from 'vds-components';

export default () => {

    const onClickHandler: React.MouseEventHandler<HTMLAnchorElement> = (ev) => console.dir(ev);

    return (
      <VdsBreadcrumb>
        <Link onClick={onClickHandler}>Breadcrumb link 1</Link>
        <Link onClick={onClickHandler}>Breadcrumb link 2</Link>
        <Typography>Text 1</Typography>
        <Link onClick={onClickHandler}>Breadcrumb link 3</Link>
        <Typography>Text 2</Typography>
      </VdsBreadcrumb>
    );
}
`)
//#endregion

//#region Examples
export const Breadcrumb_Default_Example = () => {

  const onClickHandler: React.MouseEventHandler<HTMLAnchorElement> = (ev) => console.dir(ev);

  return (
    <VdsBreadcrumb>
      <Link onClick={onClickHandler}>Breadcrumb link 1</Link>
      <Link onClick={onClickHandler}>Breadcrumb link 2</Link>
      <Link onClick={onClickHandler}>Breadcrumb link 3</Link>
      <Typography>Text 1</Typography>
    </VdsBreadcrumb>
  )
}
export const PageTitle_WithBreadcrumb_Example = () => {

  const handleBackEvent = () => console.dir('click');
  const onClickHandler: React.MouseEventHandler<HTMLAnchorElement> = (ev) => console.dir(ev);

  return (
    <VdsPageTitle
      title="PAGE TITLE"
      historyBackEvent={handleBackEvent}
      content={
        <VdsBreadcrumb>
          <Link onClick={onClickHandler}>Breadcrumb link 1</Link>
          <Link onClick={onClickHandler}>Breadcrumb link 2</Link>
          <Typography>Text 1</Typography>
        </VdsBreadcrumb>
      }
    />
  )
}
//#endregion

export default () => (
  <>
    <VdsPageTitle title='Breadcrumb' />
    <p>Breadcrumb is used to show the path of a page. This element allows the user to always know where he/she is.</p>
    <h3>Overview</h3>
    <p>Breadcrumb improves state control and helps the user navigation increasing findability through pages. It's normally placed on top of the page close to the title line.</p>
    <CodeHighlight>
      <Breadcrumb_Default_Example />
    </CodeHighlight>
    <h3>Code</h3>
    <Highlight language='typescript'>{breadcrumb_snippet}</Highlight>
    <CodeHighlight>
      <PageTitle_WithBreadcrumb_Example />
    </CodeHighlight>
    <h3>Code</h3>
    <Highlight language='typescript'>{breadcrumb_snippet}</Highlight>
  </>
)
